#!/usr/bin/env bash
set -euo pipefail

if [[ $# -lt 1 ]]; then
  echo "usage: $0 <paper-root-module>" >&2
  exit 1
fi

paper_spec="$1"
script_dir="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)"
repo_root="$(cd -- "${script_dir}/.." && pwd)"
logs_dir="${repo_root}/logs"
mkdir -p "${logs_dir}"

python3 - "${repo_root}" "${paper_spec}" "${logs_dir}" <<'PY'
from __future__ import annotations

import os
import re
import sys
from collections import deque
from pathlib import Path

repo_root = Path(sys.argv[1]).resolve()
paper_spec = sys.argv[2]
logs_dir = Path(sys.argv[3]).resolve()

MODULE_RE = re.compile(r"^\s*module\s+([A-Z][A-Za-z0-9_']*(?:\.[A-Z][A-Za-z0-9_']*)*)\b")
IMPORT_RE = re.compile(
    r"^\s*(?:open\s+(?:public\s+)?|public\s+open\s+)?import\s+"
    r"([A-Z][A-Za-z0-9_']*(?:\.[A-Z][A-Za-z0-9_']*)*)\b"
)
MODULE_TO_FILE: dict[str, list[Path]] = {}
PAPER_ALIAS_TO_MODULE = {
    "Paper1_NavierStokes": "DASHI.Physics.Closure.NSPaper1ClayTargetReceipt",
    "Paper3_YangMills": "DASHI.Physics.Closure.YMPaper3ClayTargetReceipt",
    "Paper8_Unification": "DASHI.Physics.Closure.Paper8CoreThesisReceipt",
    "VirtualPaper1Root": "DASHI.Papers.VirtualPaper1Root",
    "VirtualPaper3Root": "DASHI.Papers.VirtualPaper3Root",
}


def relpath(path: Path) -> str:
    return str(path.resolve().relative_to(repo_root))


def sanitize_tag(spec: str) -> str:
    tag = spec.strip().replace(os.sep, "_").replace("/", "_").replace("\\", "_")
    tag = tag.replace(".", "_")
    tag = re.sub(r"[^A-Za-z0-9_+-]+", "_", tag)
    tag = tag.strip("_")
    return tag or "root"


def is_agda_file(path: Path) -> bool:
    return path.is_file() and path.suffix == ".agda"


def build_module_index() -> None:
    for dirpath, dirnames, filenames in os.walk(repo_root):
        dirnames[:] = sorted(d for d in dirnames if d not in {".git", ".agda", "_build", ".cache"})
        for filename in sorted(filenames):
            if not filename.endswith(".agda"):
                continue
            path = Path(dirpath) / filename
            try:
                with path.open("r", encoding="utf-8", errors="ignore") as fh:
                    for raw_line in fh:
                        line = raw_line.split("--", 1)[0].strip()
                        if not line:
                            continue
                        match = MODULE_RE.match(line)
                        if match:
                            MODULE_TO_FILE.setdefault(match.group(1), []).append(path)
                            break
            except OSError:
                continue

    for module_name in list(MODULE_TO_FILE):
        MODULE_TO_FILE[module_name] = sorted(MODULE_TO_FILE[module_name], key=lambda p: relpath(p))


def normalize_candidate(value: str) -> list[Path]:
    raw = Path(value)
    candidates: list[Path] = []

    def add(candidate: Path) -> None:
        if candidate not in candidates:
            candidates.append(candidate)

    if raw.is_absolute():
        add(raw)
        if raw.suffix != ".agda":
            add(raw.with_suffix(".agda"))
    else:
        add(repo_root / raw)
        if raw.suffix != ".agda":
            add((repo_root / raw).with_suffix(".agda"))

    dotted = Path(*value.split("."))
    if len(dotted.parts) > 1 or "." in value:
        add(repo_root / dotted)
        add((repo_root / dotted).with_suffix(".agda"))

    if value.endswith(".agda"):
        add(repo_root / value)

    return candidates


def resolve_spec(spec: str) -> Path:
    aliased = PAPER_ALIAS_TO_MODULE.get(spec)
    if aliased is not None:
        spec = aliased

    for candidate in normalize_candidate(spec):
        if is_agda_file(candidate):
            return candidate.resolve()

    exact = MODULE_TO_FILE.get(spec)
    if exact:
        return exact[0].resolve()

    dotted = spec.replace("/", ".").replace("\\", ".")
    exact = MODULE_TO_FILE.get(dotted)
    if exact:
        return exact[0].resolve()

    stem = spec.rsplit("/", 1)[-1].rsplit("\\", 1)[-1]
    if stem.endswith(".agda"):
        stem = stem[:-5]
    for module_name, paths in MODULE_TO_FILE.items():
        if module_name.split(".")[-1] == stem:
            return paths[0].resolve()

    normalized_spec = re.sub(r"[^A-Za-z0-9]+", "", spec).lower()
    if normalized_spec:
        for module_name, paths in MODULE_TO_FILE.items():
            normalized_module = re.sub(r"[^A-Za-z0-9]+", "", module_name).lower()
            normalized_path_stem = re.sub(r"[^A-Za-z0-9]+", "", paths[0].stem).lower()
            if normalized_spec in {normalized_module, normalized_path_stem}:
                return paths[0].resolve()

    raise SystemExit(f"error: could not resolve Agda module or file: {spec}")


def parse_imports(text: str) -> list[str]:
    imports: list[str] = []
    seen: set[str] = set()
    for raw_line in text.splitlines():
        line = raw_line.split("--", 1)[0]
        match = IMPORT_RE.match(line)
        if not match:
            continue
        module = match.group(1)
        if module not in seen:
            seen.add(module)
            imports.append(module)
    return sorted(imports)


build_module_index()
root_file = resolve_spec(paper_spec)
paper_tag = sanitize_tag(paper_spec)
output_path = logs_dir / f"minimal_tree_{paper_tag}.txt"

queue = deque([root_file])
queued: set[Path] = {root_file}
visited: set[Path] = set()
ordered_files: list[Path] = []

files_processed = 0
import_lines_seen = 0
unique_import_modules = 0
resolved_import_edges = 0
missing_import_modules = 0
duplicate_resolution_hits = 0
cycle_skips = 0


def resolve_import(module_name: str) -> Path | None:
    candidates = MODULE_TO_FILE.get(module_name)
    if candidates:
        return candidates[0].resolve()
    return None


while queue:
    current = queue.popleft()
    if current in visited:
        continue
    visited.add(current)
    ordered_files.append(current)
    files_processed += 1

    try:
        text = current.read_text(encoding="utf-8", errors="ignore")
    except OSError as exc:
        raise SystemExit(f"error: unable to read {current}: {exc}") from exc

    imports = parse_imports(text)
    unique_import_modules += len(imports)
    import_lines_seen += sum(
        1 for raw_line in text.splitlines() if IMPORT_RE.match(raw_line.split("--", 1)[0])
    )

    for module_name in imports:
        resolved = resolve_import(module_name)
        if resolved is None:
            missing_import_modules += 1
            continue
        resolved = resolved.resolve()
        if resolved in visited:
            cycle_skips += 1
        elif resolved in queued:
            duplicate_resolution_hits += 1
        else:
            queue.append(resolved)
            queued.add(resolved)
            resolved_import_edges += 1

reachable_paths = [relpath(path) for path in ordered_files]
output_path.write_text("\n".join(reachable_paths) + "\n", encoding="utf-8")

print(f"root_spec: {paper_spec}")
print(f"root_file: {relpath(root_file)}")
print(f"output: {relpath(output_path)}")
print(f"reachable_files: {len(reachable_paths)}")
print(f"modules_indexed: {len(MODULE_TO_FILE)}")
print(f"import_lines_seen: {import_lines_seen}")
print(f"unique_import_modules: {unique_import_modules}")
print(f"resolved_import_edges: {resolved_import_edges}")
print(f"missing_import_modules: {missing_import_modules}")
print(f"duplicate_import_skips: {duplicate_resolution_hits}")
print(f"cycle_import_skips: {cycle_skips}")
PY
