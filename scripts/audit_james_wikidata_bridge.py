#!/usr/bin/env python3
from __future__ import annotations

import argparse
import csv
import hashlib
import pathlib
import re
import sys

DECL_LINE_RE = re.compile(
    r"^\s*(?:set_option\b.*\bin\s*)?(?:@[\[].*?[\]]\s*)?"
    r"(theorem|lemma|def|abbrev|structure|class|inductive|instance)\s+"
    r"([A-Za-z0-9_'.?«»]+)"
)
NAMESPACE_RE = re.compile(r"^\s*namespace\s+([A-Za-z0-9_.]+)\s*$")
END_RE = re.compile(r"^\s*end(?:\s+([A-Za-z0-9_.]+))?\s*$")


def sha256(path: pathlib.Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as handle:
        for chunk in iter(lambda: handle.read(1 << 20), b""):
            digest.update(chunk)
    return digest.hexdigest()


def read_tsv(path: pathlib.Path) -> list[dict[str, str]]:
    with path.open(encoding="utf-8", newline="") as handle:
        return list(csv.DictReader(handle, delimiter="\t"))


def fully_qualified_declarations(path: pathlib.Path) -> set[str]:
    """Reconstruct declared names using Lean's explicit namespace blocks.

    The supplied project uses named `end` markers for namespaces. Named section
    ends are ignored unless they match the active namespace tail. Declaration
    names may themselves contain dots or `?`, e.g. `RequiresStatement.trans`
    and `isLCS_of_lcs?_eq_some`.
    """

    namespace: list[str] = []
    declarations: set[str] = set()
    for raw_line in path.read_text(encoding="utf-8").splitlines():
        ns_match = NAMESPACE_RE.match(raw_line)
        if ns_match:
            namespace.extend(ns_match.group(1).split("."))
            continue

        end_match = END_RE.match(raw_line)
        if end_match:
            named = end_match.group(1)
            if named:
                parts = named.split(".")
                if len(parts) <= len(namespace) and namespace[-len(parts):] == parts:
                    del namespace[-len(parts):]
            continue

        decl_match = DECL_LINE_RE.match(raw_line)
        if decl_match:
            local_name = decl_match.group(2)
            declarations.add(".".join([*namespace, local_name]))

    return declarations


def main() -> int:
    parser = argparse.ArgumentParser(
        description=(
            "Verify the pinned James Michael DuPont / Aristotle Wikidata Lean "
            "source snapshot and the theorem contracts used by DASHI."
        )
    )
    parser.add_argument(
        "request_project",
        type=pathlib.Path,
        help="path to the extracted RequestProject directory from the Aristotle archive",
    )
    parser.add_argument(
        "--manifest",
        type=pathlib.Path,
        default=pathlib.Path("third_party/jmdupont_wikidata_lean/SOURCE_MANIFEST.tsv"),
    )
    parser.add_argument(
        "--contracts",
        type=pathlib.Path,
        default=pathlib.Path("third_party/jmdupont_wikidata_lean/BRIDGE_CONTRACTS.tsv"),
    )
    args = parser.parse_args()

    failures: list[str] = []
    manifest = read_tsv(args.manifest)
    actual_files = sorted(args.request_project.glob("*.lean"))
    expected = {row["module"]: row for row in manifest}

    if len(actual_files) != len(manifest):
        failures.append(
            f"module count: expected {len(manifest)}, found {len(actual_files)}"
        )

    declaration_cache: dict[str, set[str]] = {}
    for module, row in expected.items():
        path = args.request_project / f"{module}.lean"
        if not path.exists():
            failures.append(f"missing source module {path.name}")
            continue
        got_hash = sha256(path)
        if got_hash != row["sha256"]:
            failures.append(
                f"{module}: sha256 {got_hash} != pinned {row['sha256']}"
            )
        with path.open(encoding="utf-8") as handle:
            line_count = sum(1 for _ in handle)
        if line_count != int(row["lines"]):
            failures.append(
                f"{module}: line count {line_count} != pinned {row['lines']}"
            )
        declaration_cache[module] = fully_qualified_declarations(path)

    for path in actual_files:
        if path.stem not in expected:
            failures.append(f"unpinned source module {path.name}")

    contracts = read_tsv(args.contracts)
    for row in contracts:
        module = row["module"]
        theorem = row["theorem"]
        path = args.request_project / f"{module}.lean"
        if not path.exists():
            failures.append(f"contract {theorem}: source module {module} missing")
            continue
        declared = declaration_cache.get(module)
        if declared is None:
            declared = fully_qualified_declarations(path)
            declaration_cache[module] = declared
        if theorem not in declared:
            near = sorted(name for name in declared if name.endswith(theorem.rsplit(".", 1)[-1]))
            detail = f"; similarly named: {', '.join(near[:3])}" if near else ""
            failures.append(
                f"contract {theorem}: exact declaration not found in {module}.lean{detail}"
            )

    if failures:
        print("James/DASHI bridge audit FAILED", file=sys.stderr)
        for failure in failures:
            print(f" - {failure}", file=sys.stderr)
        return 1

    print(
        "James/DASHI bridge audit OK: "
        f"{len(manifest)} source modules, {len(contracts)} exact theorem contracts"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
