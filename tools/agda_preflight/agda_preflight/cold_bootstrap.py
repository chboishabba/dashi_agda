from __future__ import annotations

from dataclasses import dataclass
from concurrent.futures import ProcessPoolExecutor
import hashlib
import json
import os
from pathlib import Path
from typing import Callable, Dict, Iterable, Iterator, List, Optional, Sequence, Set, Tuple

from .ast_index import build_import_surface
from .checker import Checker, _parser
from .timing import Profiler
from .interfaces import ModuleInterface, interface_from_summary, resolve_interface_exports


@dataclass(frozen=True)
class ImportReceipt:
    path: str
    module_name: str
    imports: Tuple[str, ...]
    interface: Optional[ModuleInterface] = None
    api_base_hash: str = ""
    public_imports: Tuple[str, ...] = ()
    files_parsed: int = 0
    parse_ns: int = 0


@dataclass(frozen=True)
class DiagnosticReceipt:
    path: str
    module_name: str
    mtime_ns: int
    size: int
    source_hash: str
    imports: Tuple[str, ...]
    public_imports: Tuple[str, ...]
    api_base_hash: str
    diagnostics_json: str
    diagnostic_count: int
    files_parsed: int
    diagnostics_recomputed: int
    parse_ns: int
    diagnostics_ns: int


@dataclass(frozen=True)
class DiagnosticBatchReceipt:
    batch_index: int
    target_count: int
    dependency_surface: int
    receipts: Tuple[DiagnosticReceipt, ...]


_WORKER_ROOT: Optional[Path] = None
_WORKER_PARSER = None
_WORKER_CHECKER: Optional[Checker] = None
_WORKER_PROFILER: Optional[Profiler] = None


def worker_count(requested: int) -> int:
    if requested > 0:
        return requested
    return max(1, min(8, os.cpu_count() or 1))


def _init_import_worker(root: str) -> None:
    global _WORKER_ROOT, _WORKER_PARSER, _WORKER_CHECKER, _WORKER_PROFILER
    _WORKER_ROOT = Path(root).resolve()
    _WORKER_PARSER = None
    _WORKER_PROFILER = Profiler()
    _WORKER_CHECKER = Checker(
        _WORKER_ROOT,
        profiler=_WORKER_PROFILER,
    )


def _init_diagnostic_worker(root: str) -> None:
    global _WORKER_ROOT, _WORKER_PARSER, _WORKER_CHECKER, _WORKER_PROFILER
    _WORKER_ROOT = Path(root).resolve()
    _WORKER_PARSER = None
    _WORKER_PROFILER = Profiler()
    _WORKER_CHECKER = Checker(
        _WORKER_ROOT,
        profiler=_WORKER_PROFILER,
    )


def _scan_import(path_text: str) -> ImportReceipt:
    assert _WORKER_ROOT is not None
    assert _WORKER_CHECKER is not None
    assert _WORKER_PROFILER is not None
    before = _WORKER_PROFILER.snapshot()
    path = Path(path_text).resolve()
    summary = _WORKER_CHECKER.parse_summary(path)
    interface = interface_from_summary(_WORKER_ROOT, summary)
    api_base_hash, public_imports = _api_base(
        _WORKER_ROOT,
        summary,
    )
    after = _WORKER_PROFILER.snapshot()
    return ImportReceipt(
        path=str(path),
        module_name=summary.module_name,
        imports=tuple(sorted(set(summary.imports.values()))),
        interface=interface,
        api_base_hash=api_base_hash,
        public_imports=public_imports,
        files_parsed=(
            after.counts.get("files_parsed", 0)
            - before.counts.get("files_parsed", 0)
        ),
        parse_ns=(
            after.stages_ns.get("parse.tree_sitter", 0)
            - before.stages_ns.get("parse.tree_sitter", 0)
        ),
    )


def _directive_payload(directive) -> dict:
    return {
        "kind": directive.kind,
        "names": list(directive.names),
        "renamings": [list(pair) for pair in directive.renamings],
    }


def _api_base(root: Path, summary) -> Tuple[str, Tuple[str, ...]]:
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
                        _directive_payload(directive)
                        for directive in item.directives
                    ],
                }
            )

    public_open_payload = []
    for opened in summary.ast.opens:
        if not opened.public:
            continue
        module = summary.imports.get(opened.target)
        if module is None:
            candidate = root.joinpath(
                *opened.target.split(".")
            ).with_suffix(".agda")
            if candidate.exists():
                module = opened.target
        if module is not None:
            public_imports.add(module)
        public_open_payload.append(
            {
                "target": opened.target,
                "module": module,
                "directives": [
                    _directive_payload(directive)
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


def _diagnostic_payload(root: Path, diagnostic) -> dict:
    payload = diagnostic.as_dict()
    diagnostic_path = Path(payload["path"])
    try:
        payload["path"] = diagnostic_path.resolve().relative_to(root).as_posix()
    except ValueError:
        pass
    for fix in payload.get("fixes", []):
        for edit in fix.get("edits", []):
            edit_path = Path(edit["path"])
            try:
                edit["path"] = edit_path.resolve().relative_to(root).as_posix()
            except ValueError:
                pass
    return payload


def _diagnose_path_with(
    checker: Checker,
    profiler: Profiler,
    root: Path,
    path_text: str,
) -> DiagnosticReceipt:
    before = profiler.snapshot()
    path = Path(path_text).resolve()
    summary = checker.parse_summary(path)
    diagnostics = checker.structural_check(path)
    after = profiler.snapshot()
    stat = path.stat()
    source_hash = hashlib.sha256(
        summary.source.encode("utf-8")
    ).hexdigest()
    api_base_hash, public_imports = _api_base(
        root,
        summary,
    )
    return DiagnosticReceipt(
        path=str(path),
        module_name=summary.module_name,
        mtime_ns=stat.st_mtime_ns,
        size=stat.st_size,
        source_hash=source_hash,
        imports=tuple(sorted(set(summary.imports.values()))),
        public_imports=public_imports,
        api_base_hash=api_base_hash,
        diagnostics_json=json.dumps(
            [
                _diagnostic_payload(root, item)
                for item in diagnostics
            ],
            sort_keys=True,
            separators=(",", ":"),
        ),
        diagnostic_count=len(diagnostics),
        files_parsed=(
            after.counts.get("files_parsed", 0)
            - before.counts.get("files_parsed", 0)
        ),
        diagnostics_recomputed=(
            after.counts.get("diagnostics_recomputed", 0)
            - before.counts.get("diagnostics_recomputed", 0)
        ),
        parse_ns=(
            after.stages_ns.get("parse.tree_sitter", 0)
            - before.stages_ns.get("parse.tree_sitter", 0)
        ),
        diagnostics_ns=(
            after.stages_ns.get("diagnostics.local", 0)
            - before.stages_ns.get("diagnostics.local", 0)
        ),
    )


def _diagnose_path(path_text: str) -> DiagnosticReceipt:
    assert _WORKER_ROOT is not None
    assert _WORKER_CHECKER is not None
    assert _WORKER_PROFILER is not None
    return _diagnose_path_with(
        _WORKER_CHECKER,
        _WORKER_PROFILER,
        _WORKER_ROOT,
        path_text,
    )


def discover_closure(
    root: Path,
    target: Path,
    *,
    jobs: int = 0,
    cached_lookup: Optional[
        Callable[[Path], Optional[ImportReceipt]]
    ] = None,
) -> Tuple[ImportReceipt, ...]:
    root = root.resolve()
    target = target.resolve()
    workers = worker_count(jobs)
    seen: Dict[Path, ImportReceipt] = {}
    frontier = [target]

    with ProcessPoolExecutor(
        max_workers=workers,
        initializer=_init_import_worker,
        initargs=(str(root),),
    ) as executor:
        while frontier:
            current = [
                path for path in sorted(set(frontier))
                if path not in seen
            ]
            if not current:
                break

            cached_receipts = []
            misses = []
            for path in current:
                cached = (
                    cached_lookup(path)
                    if cached_lookup is not None
                    else None
                )
                if cached is None:
                    misses.append(path)
                else:
                    cached_receipts.append(cached)

            parsed_receipts = ()
            if misses:
                chunksize = max(
                    1,
                    len(misses) // max(1, workers * 4),
                )
                parsed_receipts = tuple(
                    executor.map(
                        _scan_import,
                        [str(path) for path in misses],
                        chunksize=chunksize,
                    )
                )

            next_frontier = []
            for receipt in (
                *cached_receipts,
                *parsed_receipts,
            ):
                path = Path(receipt.path).resolve()
                seen[path] = receipt
                for module in receipt.imports:
                    dependency = root.joinpath(
                        *module.split(".")
                    ).with_suffix(".agda")
                    if (
                        dependency.exists()
                        and dependency.resolve() not in seen
                    ):
                        next_frontier.append(dependency.resolve())
            frontier = next_frontier

    return tuple(
        seen[path]
        for path in sorted(seen)
    )


def dependency_closures(
    receipts: Sequence[ImportReceipt],
) -> Dict[str, Set[str]]:
    """Return transitive in-closure dependency sets, including each module."""
    module_names = {item.module_name for item in receipts}
    graph = {
        receipt.module_name: tuple(
            dependency
            for dependency in receipt.imports
            if dependency in module_names
        )
        for receipt in receipts
    }
    memo: Dict[str, Set[str]] = {}

    def visit(module: str, active: Set[str]) -> Set[str]:
        cached = memo.get(module)
        if cached is not None:
            return set(cached)
        if module in active:
            return {module}
        nested = set(active)
        nested.add(module)
        closure = {module}
        for dependency in graph.get(module, ()):
            closure.update(visit(dependency, nested))
        memo[module] = set(closure)
        return closure

    for module in graph:
        visit(module, set())
    return memo


def dependency_affinity_batches(
    receipts: Sequence[ImportReceipt],
    *,
    jobs: int,
    targets: Optional[Set[str]] = None,
) -> Tuple[Tuple[ImportReceipt, ...], ...]:
    """Partition targets by dependency overlap while preserving parallel load.

    The scheduler bounds target-count skew, then minimizes each assignment's
    incremental transitive dependency surface. This avoids the old arbitrary
    path chunks where shared foundations were reparsed independently by every
    worker.
    """
    if not receipts:
        return ()
    workers = max(1, min(worker_count(jobs), len(receipts)))
    closures = dependency_closures(receipts)
    by_module = {receipt.module_name: receipt for receipt in receipts}

    target_modules = (
        set(by_module)
        if targets is None
        else set(targets) & set(by_module)
    )
    ordered = sorted(
        target_modules,
        key=lambda module: (-len(closures[module]), module),
    )
    target_cap = (len(ordered) + workers - 1) // workers
    batches: List[List[str]] = [[] for _ in range(workers)]
    covered: List[Set[str]] = [set() for _ in range(workers)]

    for module in ordered:
        candidates = [
            index
            for index, batch in enumerate(batches)
            if len(batch) < target_cap
        ]
        if not candidates:
            candidates = list(range(workers))

        closure = closures[module]
        chosen = min(
            candidates,
            key=lambda index: (
                len(closure - covered[index]),
                len(covered[index]),
                len(batches[index]),
                index,
            ),
        )
        batches[chosen].append(module)
        covered[chosen].update(closure)

    result = []
    for batch in batches:
        if not batch:
            continue
        # Broad dependents first: parsing one tends to populate the Checker's
        # summary cache for modules diagnosed later in the same worker.
        batch.sort(key=lambda module: (-len(closures[module]), module))
        result.append(tuple(by_module[module] for module in batch))
    return tuple(result)


def _diagnose_batch(payload) -> DiagnosticBatchReceipt:
    (
        batch_index,
        root_text,
        path_texts,
        dependency_surface,
        interfaces,
    ) = payload
    root = Path(root_text).resolve()
    interface_map = {
        interface.module_name: interface
        for interface in interfaces
    }
    profiler = Profiler()
    checker = Checker(
        root,
        profiler=profiler,
        interfaces=interface_map,
    )
    return DiagnosticBatchReceipt(
        batch_index=batch_index,
        target_count=len(path_texts),
        dependency_surface=dependency_surface,
        receipts=tuple(
            _diagnose_path_with(
                checker,
                profiler,
                root,
                path,
            )
            for path in path_texts
        ),
    )


def diagnose_paths(
    root: Path,
    paths: Sequence[Path],
    *,
    jobs: int = 0,
    import_receipts: Optional[Sequence[ImportReceipt]] = None,
) -> Tuple[DiagnosticBatchReceipt, ...]:
    root = root.resolve()
    workers = worker_count(jobs)
    ordered = sorted({path.resolve() for path in paths})
    if not ordered:
        return ()

    if import_receipts is None:
        batches = tuple(
            (ImportReceipt(str(path), path.stem, ()),)
            for path in ordered
        )
        closure_sizes = [1 for _ in batches]
    else:
        target_paths = {path.resolve() for path in ordered}
        target_modules = {
            item.module_name
            for item in import_receipts
            if Path(item.path).resolve() in target_paths
        }
        batches = dependency_affinity_batches(
            import_receipts,
            jobs=workers,
            targets=target_modules,
        )
        closures = dependency_closures(import_receipts)
        closure_sizes = [
            len(
                set().union(
                    *(closures[item.module_name] for item in batch)
                )
            )
            for batch in batches
        ]

    raw_interfaces = {
        item.module_name: item.interface
        for item in (import_receipts or ())
        if item.interface is not None
    }
    resolved_interfaces = resolve_interface_exports(raw_interfaces)
    closures = (
        dependency_closures(import_receipts)
        if import_receipts is not None
        else {}
    )

    payloads = []
    for index, batch in enumerate(batches):
        needed = set()
        if import_receipts is not None:
            for item in batch:
                needed.update(closures[item.module_name])
        interfaces = tuple(
            resolved_interfaces[module]
            for module in sorted(needed)
            if module in resolved_interfaces
        )
        payloads.append(
            (
                index,
                str(root),
                tuple(item.path for item in batch),
                closure_sizes[index],
                interfaces,
            )
        )

    # Submit exactly one affinity batch per logical worker. Each process gets
    # immutable interfaces for its dependency cone, so only the modules being
    # diagnosed need live tree-sitter ASTs.
    with ProcessPoolExecutor(
        max_workers=min(workers, len(payloads)),
    ) as executor:
        return tuple(executor.map(_diagnose_batch, payloads))
