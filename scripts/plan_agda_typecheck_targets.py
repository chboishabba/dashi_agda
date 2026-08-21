#!/usr/bin/env python3
"""Plan the exact first-party Agda target set for repository-wide typechecking.

This is deliberately independent of the Everything import hierarchy. The
repository health question is: which maintained source files must Agda accept
before we may say "everything in the repo is typechecked"?

Known YM/NS/Balaban lanes are live but operationally heavy. They are omitted
from the default tractable run and can be included explicitly with
--include-heavy.
"""

from __future__ import annotations

import argparse
import json
from pathlib import Path
import sys

SOURCE_SUFFIXES = (".agda", ".lagda", ".lagda.md", ".lagda.rst", ".lagda.tex")

# Non-first-party/build infrastructure only. Keep narrow and explicit.
EXCLUDED_PARTS = {
    ".git",
    ".cache",
    "agda-toolchain",
    "cubical",
    "vendor",
    "monster",
    "_build",
}

# Operational exclusions, NOT non-live classifications.
HEAVY_PREFIXES = (
    "DASHI/Physics/YangMills/",
    "DASHI/Physics/Closure/",
    "DASHI/Papers/NavierStokes/",
)
HEAVY_NAME_FRAGMENTS = ("Balaban", "NavierStokes", "YangMills")

GENERATED_PREFIXES = ("DASHI/GeneratedEverything/",)
GENERATED_FILES = {"DASHI/EverythingGenerated.agda"}


def is_agda_source(rel: str) -> bool:
    return any(rel.endswith(suffix) for suffix in SOURCE_SUFFIXES)


def excluded_infrastructure(rel: str) -> bool:
    return any(part in EXCLUDED_PARTS for part in Path(rel).parts)


def operationally_heavy(rel: str) -> bool:
    return (
        any(rel.startswith(prefix) for prefix in HEAVY_PREFIXES)
        or any(fragment in rel for fragment in HEAVY_NAME_FRAGMENTS)
    )


def generated_infrastructure(rel: str) -> bool:
    return rel in GENERATED_FILES or any(rel.startswith(p) for p in GENERATED_PREFIXES)


def load_nonlive(root: Path) -> set[str]:
    manifest = root / "scripts" / "everything_nonlive.json"
    if not manifest.exists():
        return set()
    data = json.loads(manifest.read_text())
    if isinstance(data, list):
        entries = data
    elif isinstance(data, dict):
        entries = data.get("entries", data.get("nonlive", []))
    else:
        raise ValueError(f"unsupported non-live manifest shape: {manifest}")
    result: set[str] = set()
    for entry in entries:
        if isinstance(entry, str):
            result.add(entry)
        elif isinstance(entry, dict) and isinstance(entry.get("path"), str):
            result.add(entry["path"])
    return result


def discover(root: Path, include_heavy: bool) -> tuple[list[str], list[str], list[str], list[str]]:
    nonlive = load_nonlive(root)
    selected: list[str] = []
    heavy: list[str] = []
    explicit_nonlive: list[str] = []
    generated: list[str] = []

    for path in root.rglob("*"):
        if not path.is_file():
            continue
        rel = path.relative_to(root).as_posix()
        if not is_agda_source(rel) or excluded_infrastructure(rel):
            continue
        if generated_infrastructure(rel):
            generated.append(rel)
        elif rel in nonlive:
            explicit_nonlive.append(rel)
        elif not include_heavy and operationally_heavy(rel):
            heavy.append(rel)
        else:
            selected.append(rel)

    return (
        sorted(selected),
        sorted(heavy),
        sorted(explicit_nonlive),
        sorted(generated),
    )


def write_lines(path: str | None, values: list[str]) -> None:
    if path:
        Path(path).write_text("".join(f"{v}\n" for v in values))


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--root", default=".")
    parser.add_argument("--include-heavy", action="store_true")
    parser.add_argument("--output", help="write newline-delimited selected targets")
    parser.add_argument("--heavy-output", help="write operationally skipped heavy targets")
    parser.add_argument("--json", dest="json_output", help="write machine-readable summary")
    parser.add_argument("--quiet", action="store_true")
    args = parser.parse_args()

    root = Path(args.root).resolve()
    selected, heavy, explicit_nonlive, generated = discover(root, args.include_heavy)

    if args.output:
        write_lines(args.output, selected)
    else:
        print("\n".join(selected))
    write_lines(args.heavy_output, heavy)

    summary = {
        "selected": len(selected),
        "operationally_skipped_heavy": len(heavy),
        "explicit_nonlive": len(explicit_nonlive),
        "generated_infrastructure": len(generated),
        "include_heavy": args.include_heavy,
        "heavy_prefixes": list(HEAVY_PREFIXES),
        "heavy_name_fragments": list(HEAVY_NAME_FRAGMENTS),
    }
    if args.json_output:
        Path(args.json_output).write_text(json.dumps(summary, indent=2, sort_keys=True) + "\n")

    if not args.quiet:
        print(
            "Typecheck plan: "
            f"selected={len(selected)} "
            f"heavy-skipped={len(heavy)} "
            f"explicit-nonlive={len(explicit_nonlive)} "
            f"generated-infra={len(generated)}",
            file=sys.stderr,
        )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
