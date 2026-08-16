#!/usr/bin/env python3
from __future__ import annotations

import argparse
import csv
import hashlib
import pathlib
import re
import sys

DECL_RE = re.compile(
    r"^\s*(?:set_option\b.*\bin\s*)?(?:@[\[].*?[\]]\s*)?"
    r"(theorem|lemma|def|abbrev|structure|class|inductive|instance)\s+"
    r"([A-Za-z0-9_'.?«»]+)",
    re.M,
)


def sha256(path: pathlib.Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as handle:
        for chunk in iter(lambda: handle.read(1 << 20), b""):
            digest.update(chunk)
    return digest.hexdigest()


def read_tsv(path: pathlib.Path) -> list[dict[str, str]]:
    with path.open(encoding="utf-8", newline="") as handle:
        return list(csv.DictReader(handle, delimiter="\t"))


def declaration_matches(theorem: str, declared: str) -> bool:
    """Match a fully-qualified bridge name against its source-local declaration.

    Lean permits declaration names such as `RequiresStatement.trans` and names
    containing `?`, so checking only the final dot-separated leaf is too weak.
    The source-local name must be either the full name or a namespace suffix of
    the fully-qualified contract.
    """

    return theorem == declared or theorem.endswith("." + declared)


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
        declared = {
            match.group(2)
            for match in DECL_RE.finditer(path.read_text(encoding="utf-8"))
        }
        if not any(declaration_matches(theorem, name) for name in declared):
            failures.append(
                f"contract {theorem}: no matching declaration found in {module}.lean"
            )

    if failures:
        print("James/DASHI bridge audit FAILED", file=sys.stderr)
        for failure in failures:
            print(f" - {failure}", file=sys.stderr)
        return 1

    print(
        "James/DASHI bridge audit OK: "
        f"{len(manifest)} source modules, {len(contracts)} pinned theorem contracts"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
