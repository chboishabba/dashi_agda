from __future__ import annotations

from dataclasses import dataclass
import hashlib
import json
from pathlib import Path
import sqlite3
import time
from typing import Dict, Iterable, List, Optional, Set, Tuple

from .checker import Checker, Diagnostic
from .timing import Profiler


SCHEMA_VERSION = "1"


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
    imports: Tuple[str, ...]
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
    ) -> None:
        self.root = root.resolve()
        self.path = path if path.is_absolute() else self.root / path
        self.profiler = profiler or Profiler()
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
        if row is None or row["value"] != SCHEMA_VERSION:
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
        )

    def _decode_diagnostics(self, row) -> List[Diagnostic]:
        return [
            self._diagnostic_from_dict(item)
            for item in json.loads(row["diagnostics_json"])
        ]

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
        dependency_fingerprint: str,
        imports: Iterable[str],
        diagnostics: List[Diagnostic],
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
                    dependency_fingerprint, diagnostics_json, updated_ns
                )
                VALUES(?, ?, ?, ?, ?, ?, ?, ?)
                ON CONFLICT(path) DO UPDATE SET
                    module_name = excluded.module_name,
                    mtime_ns = excluded.mtime_ns,
                    size = excluded.size,
                    source_sha256 = excluded.source_sha256,
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
                    self.profiler.count("dirty_modules")
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
                source_hash = row["source_sha256"]
            else:
                checker = self._checker_instance()
                summary = checker.parse_summary(path)
                module_name = summary.module_name
                imports = tuple(sorted(set(summary.imports.values())))
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
            self._states[path] = _ModuleState(
                path=path,
                module_name=module_name,
                source_hash=source_hash,
                imports=imports,
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

            dependency_fingerprint = self._dependency_fingerprint(
                (module, state.source_hash)
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
                    dependency_fingerprint,
                    imports,
                    diagnostics,
                )

            state = _ModuleState(
                path=path,
                module_name=module_name,
                source_hash=source_hash,
                imports=imports,
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

    def diagnose(self, target: Path) -> DiagnoseResult:
        target = target if target.is_absolute() else self.root / target
        target = target.resolve()

        warm = self._warm_result(target)
        if warm is not None:
            return warm

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
