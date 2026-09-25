from __future__ import annotations

from dataclasses import dataclass
import hashlib
import json
from pathlib import Path
import sqlite3
import time
from typing import Dict, Iterable, List, Optional, Set, Tuple

from .checker import Checker, Diagnostic
from .fixes import SuggestedFix, TextEdit
from .timing import Profiler
from .cold_bootstrap import discover_closure, diagnose_paths, worker_count


SCHEMA_VERSION = "2"


@dataclass(frozen=True)
class DiagnoseResult:
    diagnostics: List[Diagnostic]
    modules: Tuple[str, ...]
    cache_hit: bool

    def as_dict(self) -> dict:
        return {
            "modules": list(self.modules),
            "cache_hit": self.cache_hit,
            "diagnostics": [diagnostic.as_dict() for diagnostic in self.diagnostics],
        }


@dataclass
class _ModuleState:
    path: Path
    module_name: str
    source_hash: str
    api_hash: str
    imports: Tuple[str, ...]
    public_imports: Tuple[str, ...]
    diagnostics: List[Diagnostic]


class SourceIndex:
    """Persistent dirty-source index for fast interactive diagnostics.

    The index is deliberately separate from Agda's semantic/interface cache.
    It stores source freshness, direct imports and already-computed structural
    diagnostics. A warm unchanged dependency rollup can therefore be served
    without constructing tree-sitter or parsing any source file.
    """

    def __init__(
        self,
        root: Path,
        path: Path,
        *,
        profiler: Optional[Profiler] = None,
        jobs: int = 1,
    ) -> None:
        self.root = root.resolve()
        self.path = path if path.is_absolute() else self.root / path
        self.profiler = profiler or Profiler()
        self.jobs = jobs
        self._checker: Optional[Checker] = None
        self._visiting: Set[Path] = set()
        self._states: Dict[Path, _ModuleState] = {}

        self.path.parent.mkdir(parents=True, exist_ok=True)
        with self.profiler.stage("db.open"):
            self.connection = sqlite3.connect(self.path)
            self.connection.row_factory = sqlite3.Row
        with self.profiler.stage("db.schema"):
            self._configure()
            self._ensure_schema()

    def close(self) -> None:
        self.connection.close()

    def __enter__(self) -> "SourceIndex":
        return self

    def __exit__(self, exc_type, exc, tb) -> None:
        self.close()

    def _configure(self) -> None:
        self.connection.execute("PRAGMA journal_mode=WAL")
        self.connection.execute("PRAGMA synchronous=NORMAL")
        self.connection.execute("PRAGMA foreign_keys=ON")
        self.connection.execute("PRAGMA temp_store=MEMORY")
        self.connection.execute("PRAGMA busy_timeout=5000")

    def _ensure_schema(self) -> None:
        self.connection.executescript(
            """
            CREATE TABLE IF NOT EXISTS meta (
                key TEXT PRIMARY KEY,
                value TEXT NOT NULL
            );

            CREATE TABLE IF NOT EXISTS modules (
                path TEXT PRIMARY KEY,
                module_name TEXT NOT NULL,
                mtime_ns INTEGER NOT NULL,
                size INTEGER NOT NULL,
                source_sha256 TEXT NOT NULL,
                api_base_sha256 TEXT NOT NULL,
                api_fingerprint TEXT NOT NULL,
                public_imports_json TEXT NOT NULL,
                dependency_fingerprint TEXT NOT NULL,
                diagnostics_json TEXT NOT NULL,
                updated_ns INTEGER NOT NULL
            );

            CREATE UNIQUE INDEX IF NOT EXISTS modules_by_name
                ON modules(module_name);

            CREATE TABLE IF NOT EXISTS imports (
                importer_path TEXT NOT NULL
                    REFERENCES modules(path) ON DELETE CASCADE,
                imported_module TEXT NOT NULL,
                PRIMARY KEY (importer_path, imported_module)
            ) WITHOUT ROWID;

            CREATE INDEX IF NOT EXISTS imports_by_module
                ON imports(imported_module);
            """
        )
        self.connection.execute(
            "INSERT OR IGNORE INTO meta(key, value) VALUES('schema_version', ?)",
            (SCHEMA_VERSION,),
        )
        row = self.connection.execute(
            "SELECT value FROM meta WHERE key = 'schema_version'"
        ).fetchone()
        version = row["value"] if row is not None else None
        if version == "1":
            columns = {
                item["name"]
                for item in self.connection.execute(
                    "PRAGMA table_info(modules)"
                ).fetchall()
            }
            if "api_base_sha256" not in columns:
                self.connection.execute(
                    "ALTER TABLE modules ADD COLUMN "
                    "api_base_sha256 TEXT NOT NULL DEFAULT ''"
                )
            if "api_fingerprint" not in columns:
                self.connection.execute(
                    "ALTER TABLE modules ADD COLUMN "
                    "api_fingerprint TEXT NOT NULL DEFAULT ''"
                )
            if "public_imports_json" not in columns:
                self.connection.execute(
                    "ALTER TABLE modules ADD COLUMN "
                    "public_imports_json TEXT NOT NULL DEFAULT '[]'"
                )
            self.connection.execute(
                "UPDATE modules SET "
                "api_base_sha256 = CASE WHEN api_base_sha256 = '' "
                "THEN source_sha256 ELSE api_base_sha256 END, "
                "api_fingerprint = CASE WHEN api_fingerprint = '' "
                "THEN source_sha256 ELSE api_fingerprint END"
            )
            self.connection.execute(
                "UPDATE meta SET value = ? WHERE key = 'schema_version'",
                (SCHEMA_VERSION,),
            )
            version = SCHEMA_VERSION
        if version != SCHEMA_VERSION:
            raise RuntimeError(
                "unsupported dashi-agda source-index schema; "
                "remove the cache or migrate it"
            )
        self.connection.commit()

    def _checker_instance(self) -> Checker:
        if self._checker is None:
            self.profiler.count("checker_instances")
            self._checker = Checker(self.root, profiler=self.profiler)
        return self._checker

    def _relative(self, path: Path) -> str:
        return path.resolve().relative_to(self.root).as_posix()

    def _module_path(self, module: str) -> Path:
        return self.root.joinpath(*module.split(".")).with_suffix(".agda")

    def _row(self, path: Path):
        return self.connection.execute(
            "SELECT * FROM modules WHERE path = ?",
            (self._relative(path),),
        ).fetchone()

    def _imports_for_path(self, relative_path: str) -> Tuple[str, ...]:
        rows = self.connection.execute(
            "SELECT imported_module FROM imports "
            "WHERE importer_path = ? ORDER BY imported_module",
            (relative_path,),
        ).fetchall()
        return tuple(row["imported_module"] for row in rows)

    def _stat(self, path: Path) -> Tuple[int, int]:
        self.profiler.count("files_stat")
        stat = path.stat()
        return stat.st_mtime_ns, stat.st_size

    @staticmethod
    def _fresh(row, stat: Tuple[int, int]) -> bool:
        return (
            row is not None
            and int(row["mtime_ns"]) == stat[0]
            and int(row["size"]) == stat[1]
        )

    def _diagnostic_dict(self, diagnostic: Diagnostic) -> dict:
        payload = diagnostic.as_dict()
        path = Path(payload["path"])
        try:
            payload["path"] = path.resolve().relative_to(self.root).as_posix()
        except ValueError:
            payload["path"] = str(path)
        return payload

    def _diagnostic_from_dict(self, payload: dict) -> Diagnostic:
        path = Path(payload["path"])
        if not path.is_absolute():
            path = self.root / path

        fixes = []
        for item in payload.get("fixes", []):
            edits = []
            for edit in item.get("edits", []):
                edit_path = Path(edit["path"])
                if not edit_path.is_absolute():
                    edit_path = self.root / edit_path
                edits.append(
                    TextEdit(
                        path=edit_path,
                        start_line=int(edit["start_line"]),
                        start_column=int(edit["start_column"]),
                        end_line=int(edit["end_line"]),
                        end_column=int(edit["end_column"]),
                        replacement=edit["replacement"],
                        start_byte=(
                            int(edit["start_byte"])
                            if edit.get("start_byte") is not None
                            else None
                        ),
                        end_byte=(
                            int(edit["end_byte"])
                            if edit.get("end_byte") is not None
                            else None
                        ),
                    )
                )
            fixes.append(
                SuggestedFix(
                    title=item["title"],
                    applicability=item["applicability"],
                    rationale=item["rationale"],
                    validation=item["validation"],
                    edits=tuple(edits),
                )
            )

        return Diagnostic(
            code=payload["code"],
            message=payload["message"],
            path=path,
            line=int(payload["line"]),
            column=int(payload.get("column", 1)),
            hint=payload.get("hint"),
            severity=payload.get("severity", "error"),
            confidence=payload.get("confidence", "high"),
            evidence=payload.get("evidence", "dashi-index"),
            minimum_evidence=payload.get("minimum_evidence", "dashi-index"),
            evidence_sufficient=bool(payload.get("evidence_sufficient", True)),
            root_cause=payload.get("root_cause"),
            explanation=payload.get("explanation"),
            expected=payload.get("expected"),
            found=payload.get("found"),
            fixes=tuple(fixes),
        )

    def _decode_diagnostics(self, row) -> List[Diagnostic]:
        return [
            self._diagnostic_from_dict(item)
            for item in json.loads(row["diagnostics_json"])
        ]

    @staticmethod
    def _directive_payload(directive) -> dict:
        return {
            "kind": directive.kind,
            "names": list(directive.names),
            "renamings": [list(pair) for pair in directive.renamings],
        }

    def _api_base(self, summary) -> Tuple[str, Tuple[str, ...]]:
        public_imports = set()
        public_import_payload = []
        for item in summary.ast.imports:
            if item.opened and item.public:
                public_imports.add(item.module)
                public_import_payload.append(
                    {
                        "module": item.module,
                        "alias": item.alias,
                        "directives": [
                            self._directive_payload(directive)
                            for directive in item.directives
                        ],
                    }
                )

        public_open_payload = []
        for opened in summary.ast.opens:
            if not opened.public:
                continue
            module = summary.imports.get(opened.target)
            if module is None and self._module_path(opened.target).exists():
                module = opened.target
            if module is not None:
                public_imports.add(module)
            public_open_payload.append(
                {
                    "target": opened.target,
                    "module": module,
                    "directives": [
                        self._directive_payload(directive)
                        for directive in opened.directives
                    ],
                }
            )

        payload = {
            "module": summary.module_name,
            "signatures": [
                [name, signature.type_text]
                for name, signature in sorted(summary.ast.signatures.items())
            ],
            "records": [
                [
                    name,
                    record.constructor,
                    record.field_surface_complete,
                    [
                        [field_name, field.type_text]
                        for field_name, field in sorted(record.fields.items())
                    ],
                ]
                for name, record in sorted(summary.ast.records.items())
            ],
            "data": [
                [
                    name,
                    [
                        [constructor_name, constructor.type_text]
                        for constructor_name, constructor
                        in sorted(data.constructors.items())
                    ],
                ]
                for name, data in sorted(summary.ast.data.items())
            ],
            "nested_modules": sorted(summary.ast.nested_modules),
            "public_imports": sorted(
                public_import_payload,
                key=lambda item: (item["module"], item["alias"]),
            ),
            "public_opens": sorted(
                public_open_payload,
                key=lambda item: (item["target"], item["module"] or ""),
            ),
        }
        encoded = json.dumps(
            payload,
            sort_keys=True,
            separators=(",", ":"),
        ).encode("utf-8")
        return hashlib.sha256(encoded).hexdigest(), tuple(sorted(public_imports))

    @staticmethod
    def _api_fingerprint(
        api_base_hash: str,
        public_dependencies: Iterable[Tuple[str, str]],
    ) -> str:
        digest = hashlib.sha256()
        digest.update(api_base_hash.encode("ascii"))
        digest.update(b"\n")
        for module, api_hash in sorted(public_dependencies):
            digest.update(module.encode("utf-8"))
            digest.update(b"\0")
            digest.update(api_hash.encode("ascii"))
            digest.update(b"\n")
        return digest.hexdigest()

    @staticmethod
    def _dependency_fingerprint(
        dependencies: Iterable[Tuple[str, str]],
    ) -> str:
        digest = hashlib.sha256()
        for module, source_hash in sorted(dependencies):
            digest.update(module.encode("utf-8"))
            digest.update(b"\0")
            digest.update(source_hash.encode("ascii"))
            digest.update(b"\n")
        return digest.hexdigest()

    def _store(
        self,
        path: Path,
        module_name: str,
        stat: Tuple[int, int],
        source_hash: str,
        api_base_hash: str,
        api_hash: str,
        public_imports: Iterable[str],
        dependency_fingerprint: str,
        imports: Iterable[str],
        diagnostics: List[Diagnostic],
        *,
        commit: bool = True,
    ) -> None:
        relative = self._relative(path)
        payload = json.dumps(
            [self._diagnostic_dict(item) for item in diagnostics],
            sort_keys=True,
            separators=(",", ":"),
        )
        with self.profiler.stage("db.write"):
            self.connection.execute(
                """
                INSERT INTO modules(
                    path, module_name, mtime_ns, size, source_sha256,
                    api_base_sha256, api_fingerprint, public_imports_json,
                    dependency_fingerprint, diagnostics_json, updated_ns
                )
                VALUES(?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?)
                ON CONFLICT(path) DO UPDATE SET
                    module_name = excluded.module_name,
                    mtime_ns = excluded.mtime_ns,
                    size = excluded.size,
                    source_sha256 = excluded.source_sha256,
                    api_base_sha256 = excluded.api_base_sha256,
                    api_fingerprint = excluded.api_fingerprint,
                    public_imports_json = excluded.public_imports_json,
                    dependency_fingerprint = excluded.dependency_fingerprint,
                    diagnostics_json = excluded.diagnostics_json,
                    updated_ns = excluded.updated_ns
                """,
                (
                    relative,
                    module_name,
                    stat[0],
                    stat[1],
                    source_hash,
                    api_base_hash,
                    api_hash,
                    json.dumps(sorted(set(public_imports))),
                    dependency_fingerprint,
                    payload,
                    time.time_ns(),
                ),
            )
            self.connection.execute(
                "DELETE FROM imports WHERE importer_path = ?",
                (relative,),
            )
            self.connection.executemany(
                "INSERT INTO imports(importer_path, imported_module) VALUES(?, ?)",
                [(relative, module) for module in sorted(set(imports))],
            )
            if commit:
                self.connection.commit()

    def _cached_closure(self, target: Path) -> Optional[List[sqlite3.Row]]:
        target_rel = self._relative(target)
        with self.profiler.stage("closure.lookup"):
            rows = self.connection.execute(
                """
                WITH RECURSIVE closure(path, module_name) AS (
                    SELECT path, module_name
                    FROM modules
                    WHERE path = ?
                    UNION
                    SELECT m.path, m.module_name
                    FROM closure c
                    JOIN imports i ON i.importer_path = c.path
                    JOIN modules m ON m.module_name = i.imported_module
                )
                SELECT m.*
                FROM closure c
                JOIN modules m ON m.path = c.path
                ORDER BY m.module_name
                """,
                (target_rel,),
            ).fetchall()
        if not rows:
            return None
        return rows

    def _warm_result(self, target: Path) -> Optional[DiagnoseResult]:
        rows = self._cached_closure(target)
        if rows is None:
            self.profiler.count("closure_cache_miss")
            return None

        diagnostics: List[Diagnostic] = []
        modules: List[str] = []

        with self.profiler.stage("source.stat"):
            for row in rows:
                path = self.root / row["path"]
                try:
                    stat = self._stat(path)
                except OSError:
                    self.profiler.count("closure_cache_miss")
                    return None
                if not self._fresh(row, stat):
                    self.profiler.count("closure_cache_miss")
                    return None
                modules.append(row["module_name"])
                decoded = self._decode_diagnostics(row)
                diagnostics.extend(decoded)
                self.profiler.count("diagnostics_cached", len(decoded))
                self.profiler.count("modules_cached")

        self.profiler.count("closure_cache_hit")
        self.profiler.count("modules_in_closure", len(rows))
        return DiagnoseResult(
            diagnostics=sorted(
                diagnostics,
                key=lambda item: (str(item.path), item.line, item.column, item.code),
            ),
            modules=tuple(modules),
            cache_hit=True,
        )

    def _ensure_module(self, path: Path) -> _ModuleState:
        path = path.resolve()
        existing = self._states.get(path)
        if existing is not None:
            return existing

        if path in self._visiting:
            # A provisional state is installed before dependency recursion, so
            # a cold import cycle can safely reuse it without requiring a
            # previously persisted row.
            provisional = self._states.get(path)
            if provisional is None:
                raise RuntimeError(
                    "internal source-index invariant: visiting module has no provisional state"
                )
            return provisional

        self._visiting.add(path)
        try:
            stat = self._stat(path)
            row = self._row(path)
            fresh = self._fresh(row, stat)

            if fresh:
                module_name = row["module_name"]
                imports = self._imports_for_path(row["path"])
                public_imports = tuple(
                    json.loads(row["public_imports_json"])
                )
                source_hash = row["source_sha256"]
                api_base_hash = row["api_base_sha256"]
            else:
                checker = self._checker_instance()
                summary = checker.parse_summary(path)
                module_name = summary.module_name
                imports = tuple(sorted(set(summary.imports.values())))
                api_base_hash, public_imports = self._api_base(summary)
                with self.profiler.stage("source.hash"):
                    source_hash = hashlib.sha256(
                        summary.source.encode("utf-8")
                    ).hexdigest()
                self.profiler.count("dirty_modules")

            provisional_diagnostics = (
                self._decode_diagnostics(row)
                if fresh and row is not None
                else []
            )
            provisional_api_hash = (
                row["api_fingerprint"]
                if fresh and row is not None
                else api_base_hash
            )
            self._states[path] = _ModuleState(
                path=path,
                module_name=module_name,
                source_hash=source_hash,
                api_hash=provisional_api_hash,
                imports=imports,
                public_imports=public_imports,
                diagnostics=provisional_diagnostics,
            )

            dependency_states: List[Tuple[str, _ModuleState]] = []
            for module in imports:
                dependency_path = self._module_path(module)
                if not dependency_path.exists():
                    continue
                dependency_states.append(
                    (module, self._ensure_module(dependency_path))
                )

            dependency_by_module = {
                module: state
                for module, state in dependency_states
            }
            api_hash = self._api_fingerprint(
                api_base_hash,
                (
                    (module, dependency_by_module[module].api_hash)
                    for module in public_imports
                    if module in dependency_by_module
                ),
            )
            dependency_fingerprint = self._dependency_fingerprint(
                (module, state.api_hash)
                for module, state in dependency_states
            )

            if (
                fresh
                and row is not None
                and row["dependency_fingerprint"] == dependency_fingerprint
            ):
                diagnostics = self._decode_diagnostics(row)
                self.profiler.count("modules_cached")
                self.profiler.count("diagnostics_cached", len(diagnostics))
            else:
                checker = self._checker_instance()
                diagnostics = checker.structural_check(path)
                self._store(
                    path,
                    module_name,
                    stat,
                    source_hash,
                    api_base_hash,
                    api_hash,
                    public_imports,
                    dependency_fingerprint,
                    imports,
                    diagnostics,
                )

            state = _ModuleState(
                path=path,
                module_name=module_name,
                source_hash=source_hash,
                api_hash=api_hash,
                imports=imports,
                public_imports=public_imports,
                diagnostics=diagnostics,
            )
            self._states[path] = state
            return state
        finally:
            self._visiting.remove(path)

    def _collect_states(self, target: Path) -> List[_ModuleState]:
        root_state = self._ensure_module(target)
        result: Dict[str, _ModuleState] = {}

        def visit(state: _ModuleState) -> None:
            if state.module_name in result:
                return
            result[state.module_name] = state
            for module in state.imports:
                dependency = self._states.get(self._module_path(module).resolve())
                if dependency is not None:
                    visit(dependency)

        visit(root_state)
        return [result[name] for name in sorted(result)]

    def _parallel_bootstrap(self, target: Path) -> DiagnoseResult:
        workers = worker_count(self.jobs)
        with self.profiler.stage("cold.import_discovery"):
            import_receipts = discover_closure(
                self.root,
                target,
                jobs=workers,
            )
        paths = tuple(Path(item.path) for item in import_receipts)
        self.profiler.count("cold_workers", workers)
        self.profiler.count("cold_modules_discovered", len(paths))

        with self.profiler.stage("cold.parallel_diagnostics"):
            receipts = diagnose_paths(
                self.root,
                paths,
                jobs=workers,
            )
        self.profiler.count("files_parsed", len(receipts))
        self.profiler.count("diagnostics_recomputed", len(receipts))

        by_module = {
            receipt.module_name: receipt
            for receipt in receipts
        }
        api_memo: Dict[str, str] = {}

        def resolve_api(module: str, visiting: Set[str]) -> str:
            cached = api_memo.get(module)
            if cached is not None:
                return cached
            receipt = by_module[module]
            if module in visiting:
                # Public re-export cycles are rare; use the local API base at
                # the cycle edge so the resulting fingerprint stays finite and
                # deterministic under sorted traversal.
                return receipt.api_base_hash
            nested = set(visiting)
            nested.add(module)
            value = self._api_fingerprint(
                receipt.api_base_hash,
                (
                    (dependency, resolve_api(dependency, nested))
                    for dependency in sorted(receipt.public_imports)
                    if dependency in by_module
                ),
            )
            api_memo[module] = value
            return value

        for module in sorted(by_module):
            resolve_api(module, set())

        states: Dict[str, _ModuleState] = {}
        all_diagnostics: List[Diagnostic] = []

        with self.profiler.stage("db.batch_write"):
            self.connection.execute("BEGIN")
            try:
                for module in sorted(by_module):
                    receipt = by_module[module]
                    api_hash = api_memo[module]
                    dependency_fingerprint = self._dependency_fingerprint(
                        (
                            dependency,
                            api_memo[dependency],
                        )
                        for dependency in receipt.imports
                        if dependency in api_memo
                    )
                    diagnostics = [
                        self._diagnostic_from_dict(item)
                        for item in receipt.diagnostics
                    ]
                    path = Path(receipt.path)
                    self._store(
                        path,
                        receipt.module_name,
                        (receipt.mtime_ns, receipt.size),
                        receipt.source_hash,
                        receipt.api_base_hash,
                        api_hash,
                        receipt.public_imports,
                        dependency_fingerprint,
                        receipt.imports,
                        diagnostics,
                        commit=False,
                    )
                    state = _ModuleState(
                        path=path,
                        module_name=receipt.module_name,
                        source_hash=receipt.source_hash,
                        api_hash=api_hash,
                        imports=receipt.imports,
                        public_imports=receipt.public_imports,
                        diagnostics=diagnostics,
                    )
                    states[module] = state
                    self._states[path.resolve()] = state
                    all_diagnostics.extend(diagnostics)
                self.connection.commit()
            except Exception:
                self.connection.rollback()
                raise

        self.profiler.count("modules_in_closure", len(states))
        return DiagnoseResult(
            diagnostics=sorted(
                all_diagnostics,
                key=lambda item: (
                    str(item.path),
                    item.line,
                    item.column,
                    item.code,
                ),
            ),
            modules=tuple(sorted(states)),
            cache_hit=False,
        )


    def diagnose(self, target: Path) -> DiagnoseResult:
        target = target if target.is_absolute() else self.root / target
        target = target.resolve()

        warm = self._warm_result(target)
        if warm is not None:
            return warm

        if self.jobs != 1 and self._row(target) is None:
            return self._parallel_bootstrap(target)

        with self.profiler.stage("closure.refresh"):
            states = self._collect_states(target)
        self.profiler.count("modules_in_closure", len(states))
        diagnostics = [
            diagnostic
            for state in states
            for diagnostic in state.diagnostics
        ]
        return DiagnoseResult(
            diagnostics=sorted(
                diagnostics,
                key=lambda item: (str(item.path), item.line, item.column, item.code),
            ),
            modules=tuple(state.module_name for state in states),
            cache_hit=False,
        )
