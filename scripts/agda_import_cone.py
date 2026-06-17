#!/usr/bin/env python3
from __future__ import annotations

import argparse
import json
import re
import sys
from collections import defaultdict, deque
from dataclasses import dataclass
from pathlib import Path
from typing import Iterable


MODULE_DECL_RE = re.compile(r"^\s*module\s+(?P<name>[^\s{]+)\b")
IMPORT_LINE_RE = re.compile(r"^\s*(?:open\s+)?import\s+(?P<name>[^\s(]+)")


@dataclass(frozen=True)
class ModuleRecord:
    path: Path
    module: str
    imports: tuple[str, ...]


@dataclass(frozen=True)
class DependencyIndex:
    repo_root: Path
    files: tuple[ModuleRecord, ...]
    module_to_record: dict[str, ModuleRecord]
    path_to_module: dict[Path, str]
    direct_imports: dict[str, tuple[str, ...]]
    reverse_imports: dict[str, tuple[str, ...]]


def strip_agda_comments(text: str) -> str:
    out: list[str] = []
    i = 0
    depth = 0
    length = len(text)

    while i < length:
        if depth == 0 and text.startswith("--", i):
            while i < length and text[i] != "\n":
                i += 1
            continue

        if depth == 0 and text.startswith("{-", i):
            depth = 1
            i += 2
            continue

        if depth > 0 and text.startswith("{-", i):
            depth += 1
            i += 2
            continue

        if depth > 0 and text.startswith("-}", i):
            depth -= 1
            i += 2
            continue

        ch = text[i]
        if depth == 0:
            out.append(ch)
        elif ch == "\n":
            out.append("\n")
        i += 1

    return "".join(out)


def parse_module_name(lines: Iterable[str], fallback: str) -> str:
    for line in lines:
        match = MODULE_DECL_RE.match(line)
        if not match:
            continue
        name = match.group("name").strip()
        if name != "_":
            return name
    return fallback


def parse_imports(lines: Iterable[str]) -> list[str]:
    imports: list[str] = []
    for line in lines:
        match = IMPORT_LINE_RE.match(line)
        if not match:
            continue
        module = match.group("name").rstrip(";")
        if module:
            imports.append(module)
    return imports


def module_name_from_path(path: Path, repo_root: Path) -> str:
    relative = path.relative_to(repo_root)
    parts = list(relative.with_suffix("").parts)
    return ".".join(parts)


def parse_agda_file(path: Path, repo_root: Path) -> ModuleRecord:
    text = path.read_text(encoding="utf-8")
    stripped = strip_agda_comments(text)
    lines = stripped.splitlines()
    fallback = module_name_from_path(path, repo_root)
    module = parse_module_name(lines, fallback)
    imports = tuple(sorted(dict.fromkeys(parse_imports(lines))))
    return ModuleRecord(path=path, module=module, imports=imports)


def iter_agda_files(repo_root: Path) -> list[Path]:
    files = [
        path
        for path in repo_root.rglob("*.agda")
        if path.is_file() and ".git" not in path.parts
    ]
    return sorted(files)


def build_dependency_index(repo_root: Path) -> DependencyIndex:
    files: list[ModuleRecord] = []
    module_to_record: dict[str, ModuleRecord] = {}
    path_to_module: dict[Path, str] = {}
    direct_imports: dict[str, tuple[str, ...]] = {}
    reverse_imports: dict[str, set[str]] = defaultdict(set)

    for path in iter_agda_files(repo_root):
        record = parse_agda_file(path, repo_root)
        files.append(record)
        path_to_module[record.path] = record.module
        direct_imports[record.module] = record.imports
        module_to_record.setdefault(record.module, record)
        for imported in record.imports:
            reverse_imports[imported].add(record.module)

    frozen_reverse = {
        module: tuple(sorted(importers))
        for module, importers in reverse_imports.items()
    }
    return DependencyIndex(
        repo_root=repo_root,
        files=tuple(files),
        module_to_record=module_to_record,
        path_to_module=path_to_module,
        direct_imports=direct_imports,
        reverse_imports=frozen_reverse,
    )


def resolve_query_target(
    index: DependencyIndex,
    *,
    module: str | None,
    path: str | None,
) -> tuple[str, Path | None, str]:
    resolved_module: str | None = module
    resolved_path: Path | None = None
    resolution_source = "module"

    if path:
        raw_path = Path(path)
        if raw_path.is_absolute():
            candidates = [raw_path.resolve()]
        else:
            candidates = [
                (Path.cwd() / raw_path).resolve(),
                (index.repo_root / raw_path).resolve(),
            ]
        candidate = next((item for item in candidates if item.exists()), candidates[0])
        try:
            relative = candidate.relative_to(index.repo_root)
        except ValueError as exc:
            raise ValueError(f"path is outside repo root: {candidate}") from exc
        if not candidate.exists():
            raise FileNotFoundError(candidate)
        resolved_path = candidate
        path_module = index.path_to_module.get(candidate)
        if path_module is None:
            path_module = module_name_from_path(candidate, index.repo_root)
        if resolved_module is None:
            resolved_module = path_module
            resolution_source = "path"
        elif resolved_module != path_module:
            raise ValueError(
                "module/path target mismatch: "
                f"{resolved_module!r} != {path_module!r} for {relative}"
            )

    if resolved_module is None:
        raise ValueError("provide --module and/or --path")

    record = index.module_to_record.get(resolved_module)
    if record is not None:
        resolved_path = record.path
    return resolved_module, resolved_path, resolution_source


def reverse_cone(index: DependencyIndex, module: str) -> tuple[str, ...]:
    seen = {module}
    queue: deque[str] = deque(index.reverse_imports.get(module, ()))
    cone: list[str] = []

    while queue:
        current = queue.popleft()
        if current in seen:
            continue
        seen.add(current)
        cone.append(current)
        for importer in index.reverse_imports.get(current, ()):
            if importer not in seen:
                queue.append(importer)

    return tuple(sorted(cone))


def format_module_label(index: DependencyIndex, module: str) -> str:
    record = index.module_to_record.get(module)
    if record is None:
        return module
    relative = record.path.relative_to(index.repo_root)
    return f"{module} [{relative}]"


def truncate(items: list[str], limit: int | None) -> tuple[list[str], int]:
    if limit is None or limit < 0 or len(items) <= limit:
        return items, 0
    return items[:limit], len(items) - limit


def build_report(
    index: DependencyIndex,
    *,
    module: str,
    path: Path | None,
    limit: int | None,
) -> dict[str, object]:
    direct = list(index.direct_imports.get(module, ()))
    importers = sorted(index.reverse_imports.get(module, ()))
    cone = list(reverse_cone(index, module))

    direct_display, direct_hidden = truncate(direct, limit)
    importers_display, importers_hidden = truncate(importers, limit)
    cone_display, cone_hidden = truncate(cone, limit)

    record = index.module_to_record.get(module)
    target_path = record.path if record else path

    return {
        "repo_root": str(index.repo_root),
        "target": {
            "module": module,
            "path": str(target_path.relative_to(index.repo_root)) if target_path else None,
        },
        "stats": {
            "files": len(index.files),
            "modules": len(index.module_to_record),
            "import_edges": sum(len(items) for items in index.direct_imports.values()),
        },
        "direct_import_count": len(direct),
        "direct_imports": direct_display,
        "direct_imports_truncated": direct_hidden,
        "direct_importer_count": len(importers),
        "direct_importers": importers_display,
        "direct_importers_truncated": importers_hidden,
        "reverse_cone_count": len(cone),
        "reverse_cone": cone_display,
        "reverse_cone_truncated": cone_hidden,
    }


def render_text(index: DependencyIndex, report: dict[str, object]) -> str:
    target = report["target"]  # type: ignore[index]
    assert isinstance(target, dict)
    module = str(target["module"])
    path = target.get("path")
    lines = [f"Target: {module}"]
    if path:
        lines.append(f"Path: {path}")

    stats = report["stats"]  # type: ignore[index]
    assert isinstance(stats, dict)
    lines.append(
        "Corpus: "
        f"{stats['files']} files, {stats['modules']} modules, {stats['import_edges']} import edges"
    )

    direct_import_count = int(report["direct_import_count"])
    direct_imports = report["direct_imports"]  # type: ignore[index]
    assert isinstance(direct_imports, list)
    lines.append(f"Direct imports ({direct_import_count}):")
    if direct_imports:
        for item in direct_imports:
            lines.append(f"  - {item}")
        hidden = int(report["direct_imports_truncated"])
        if hidden:
            lines.append(f"  - ... ({hidden} more)")
    else:
        lines.append("  - (none)")

    importer_count = int(report["direct_importer_count"])
    importers = report["direct_importers"]  # type: ignore[index]
    assert isinstance(importers, list)
    lines.append(f"Direct importers ({importer_count}):")
    if importers:
        for importer in importers:
            lines.append(f"  - {format_module_label(index, importer)}")
        hidden = int(report["direct_importers_truncated"])
        if hidden:
            lines.append(f"  - ... ({hidden} more)")
    else:
        lines.append("  - (none)")

    cone_count = int(report["reverse_cone_count"])
    cone = report["reverse_cone"]  # type: ignore[index]
    assert isinstance(cone, list)
    lines.append(f"Transitive reverse cone ({cone_count}):")
    if cone:
        for item in cone:
            lines.append(f"  - {format_module_label(index, item)}")
        hidden = int(report["reverse_cone_truncated"])
        if hidden:
            lines.append(f"  - ... ({hidden} more)")
    else:
        lines.append("  - (none)")

    return "\n".join(lines)


def parse_args(argv: list[str]) -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description=(
            "Inspect Agda import cones in this repository and report direct "
            "importers plus the transitive reverse blast radius."
        )
    )
    parser.add_argument("--module", help="Target Agda module name.")
    parser.add_argument(
        "--path",
        help="Target Agda file path, resolved relative to the repository root or cwd.",
    )
    parser.add_argument(
        "--json",
        action="store_true",
        help="Emit machine-readable JSON instead of text.",
    )
    parser.add_argument(
        "--limit",
        type=int,
        default=50,
        help="Maximum number of importers/cone members to list. Default: 50.",
    )
    return parser.parse_args(argv)


def main(argv: list[str] | None = None) -> int:
    args = parse_args(sys.argv[1:] if argv is None else argv)
    repo_root = Path(__file__).resolve().parents[1]

    if args.limit is not None and args.limit < 0:
        print("agda-import-cone: --limit must be non-negative", file=sys.stderr)
        return 2

    try:
        index = build_dependency_index(repo_root)
        module, path, _ = resolve_query_target(
            index,
            module=args.module,
            path=args.path,
        )
        report = build_report(
            index,
            module=module,
            path=path,
            limit=args.limit,
        )
    except (OSError, ValueError) as exc:
        print(f"agda-import-cone: {exc}", file=sys.stderr)
        return 1

    if args.json:
        json.dump(report, sys.stdout, indent=2, sort_keys=True)
        sys.stdout.write("\n")
    else:
        sys.stdout.write(render_text(index, report) + "\n")

    return 0


if __name__ == "__main__":
    raise SystemExit(main())
