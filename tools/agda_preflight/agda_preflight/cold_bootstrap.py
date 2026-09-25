from __future__ import annotations

from dataclasses import dataclass
from concurrent.futures import ProcessPoolExecutor
import hashlib
import json
import os
from pathlib import Path
from typing import Dict, Iterable, Iterator, List, Sequence, Tuple

from .ast_index import build_import_surface
from .checker import Checker, _parser


@dataclass(frozen=True)
class ImportReceipt:
    path: str
    module_name: str
    imports: Tuple[str, ...]


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
    diagnostics: Tuple[dict, ...]


_WORKER_ROOT: Path | None = None
_WORKER_PARSER = None
_WORKER_CHECKER: Checker | None = None


def worker_count(requested: int) -> int:
    if requested > 0:
        return requested
    return max(1, min(8, os.cpu_count() or 1))


def _init_import_worker(root: str) -> None:
    global _WORKER_ROOT, _WORKER_PARSER, _WORKER_CHECKER
    _WORKER_ROOT = Path(root).resolve()
    _WORKER_PARSER = _parser()
    _WORKER_CHECKER = None


def _init_diagnostic_worker(root: str) -> None:
    global _WORKER_ROOT, _WORKER_PARSER, _WORKER_CHECKER
    _WORKER_ROOT = Path(root).resolve()
    _WORKER_PARSER = None
    _WORKER_CHECKER = Checker(_WORKER_ROOT)


def _scan_import(path_text: str) -> ImportReceipt:
    assert _WORKER_ROOT is not None
    assert _WORKER_PARSER is not None
    path = Path(path_text).resolve()
    source = path.read_text(encoding="utf-8")
    surface = build_import_surface(
        _WORKER_PARSER,
        path,
        _WORKER_ROOT,
        source,
    )
    return ImportReceipt(
        path=str(path),
        module_name=surface.module_name,
        imports=tuple(
            sorted({item.module for item in surface.imports})
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


def _diagnose_path(path_text: str) -> DiagnosticReceipt:
    assert _WORKER_ROOT is not None
    assert _WORKER_CHECKER is not None
    path = Path(path_text).resolve()
    summary = _WORKER_CHECKER.parse_summary(path)
    diagnostics = _WORKER_CHECKER.structural_check(path)
    stat = path.stat()
    source_hash = hashlib.sha256(
        summary.source.encode("utf-8")
    ).hexdigest()
    api_base_hash, public_imports = _api_base(
        _WORKER_ROOT,
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
        diagnostics=tuple(item.as_dict() for item in diagnostics),
    )


def discover_closure(
    root: Path,
    target: Path,
    *,
    jobs: int = 0,
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
            chunksize = max(1, len(current) // max(1, workers * 4))
            receipts = executor.map(
                _scan_import,
                [str(path) for path in current],
                chunksize=chunksize,
            )
            next_frontier = []
            for receipt in receipts:
                path = Path(receipt.path).resolve()
                seen[path] = receipt
                for module in receipt.imports:
                    dependency = root.joinpath(
                        *module.split(".")
                    ).with_suffix(".agda")
                    if dependency.exists() and dependency.resolve() not in seen:
                        next_frontier.append(dependency.resolve())
            frontier = next_frontier

    return tuple(
        seen[path]
        for path in sorted(seen)
    )


def diagnose_paths(
    root: Path,
    paths: Sequence[Path],
    *,
    jobs: int = 0,
) -> Tuple[DiagnosticReceipt, ...]:
    root = root.resolve()
    workers = worker_count(jobs)
    ordered = sorted({path.resolve() for path in paths})
    if not ordered:
        return ()

    # Each worker keeps one Checker alive across its chunk of work. Imported
    # summaries therefore remain cached within the process instead of creating
    # one parser/checker per submitted module.
    chunksize = max(1, len(ordered) // max(1, workers * 2))
    with ProcessPoolExecutor(
        max_workers=workers,
        initializer=_init_diagnostic_worker,
        initargs=(str(root),),
    ) as executor:
        receipts = executor.map(
            _diagnose_path,
            [str(path) for path in ordered],
            chunksize=chunksize,
        )
        return tuple(receipts)
