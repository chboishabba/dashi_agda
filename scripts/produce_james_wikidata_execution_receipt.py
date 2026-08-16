#!/usr/bin/env python3
from __future__ import annotations

"""Produce a content-addressed James/DASHI theorem execution receipt.

This is deliberately a *local producer*, not a GitHub Action.  It requires the
user-supplied RequestProject source tree to be present locally because the
snapshot has no license file and therefore is not vendored into this repo.

The producer does three independent checks before writing a receipt:

1. every RequestProject/*.lean file matches the pinned SOURCE_MANIFEST.tsv hash;
2. the requested (module, theorem, polarity) is in BRIDGE_CONTRACTS.tsv;
3. Lean successfully elaborates a generated source file importing that module
   and `#check`ing the exact fully-qualified theorem name.

The canonical graph hash is bound into the output receipt.  Important boundary:
`#check theorem` establishes that the pinned theorem elaborates in the supplied
Lean development; it does NOT prove that an arbitrary external TSV was parsed by
James's checker.  For the current worked fixtures the graph/Theorem association
is the separately reviewed bridge mapping.  A future executable graph loader can
strengthen that seam without changing the receipt verifier contract.
"""

import argparse
import csv
import hashlib
import json
import os
import pathlib
import shutil
import subprocess
import sys
import tempfile
from typing import Iterable

REQUEST_ID = "ae06ae06-2580-422a-8fc3-92aeaaca8762"
ARCHIVE_SHA256 = "d394cd224742dea06a47d2cc6c150e9284e2d6ea291a02c3ba2b2dd04d4f5f88"
CONTRACT = "dashi.james_wikidata_execution.v1"


def sha256(path: pathlib.Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as handle:
        for chunk in iter(lambda: handle.read(1 << 20), b""):
            digest.update(chunk)
    return digest.hexdigest()


def load_manifest(path: pathlib.Path) -> list[dict[str, str]]:
    with path.open(encoding="utf-8", newline="") as handle:
        rows = list(csv.DictReader(handle, delimiter="\t"))
    if not rows:
        raise ValueError("SOURCE_MANIFEST.tsv is empty")
    return rows


def verify_source_tree(source_root: pathlib.Path, rows: Iterable[dict[str, str]]) -> None:
    missing: list[str] = []
    mismatched: list[str] = []
    for row in rows:
        module = row["module"]
        expected = row["sha256"]
        source = source_root / "RequestProject" / f"{module}.lean"
        if not source.is_file():
            missing.append(str(source))
            continue
        actual = sha256(source)
        if actual != expected:
            mismatched.append(f"{source}: expected {expected}, actual {actual}")
    if missing or mismatched:
        parts: list[str] = []
        if missing:
            parts.append("missing source files:\n  " + "\n  ".join(missing))
        if mismatched:
            parts.append("source hash mismatches:\n  " + "\n  ".join(mismatched))
        raise ValueError("\n".join(parts))


def load_contracts(path: pathlib.Path) -> set[tuple[str, str, str]]:
    with path.open(encoding="utf-8", newline="") as handle:
        return {
            (row["module"], row["theorem"], row["polarity"])
            for row in csv.DictReader(handle, delimiter="\t")
        }


def resolve_lean_command(source_root: pathlib.Path, explicit: str | None) -> list[str]:
    if explicit:
        return explicit.split()
    lakefile_candidates = [source_root / "lakefile.lean", source_root / "lakefile.toml"]
    if any(path.exists() for path in lakefile_candidates) and shutil.which("lake"):
        return ["lake", "env", "lean"]
    lean = shutil.which("lean")
    if lean:
        return [lean]
    raise ValueError(
        "no Lean executable found; install Lean/lake or pass --lean-command, "
        "for example --lean-command 'lake env lean'"
    )


def check_theorem(
    source_root: pathlib.Path,
    module: str,
    theorem: str,
    lean_command: list[str],
) -> None:
    source = f"import RequestProject.{module}\n\n#check {theorem}\n"
    with tempfile.TemporaryDirectory(prefix="dashi-james-lean-") as tmp:
        runner = pathlib.Path(tmp) / "DashiReceiptCheck.lean"
        runner.write_text(source, encoding="utf-8")
        env = os.environ.copy()
        # Lean resolves RequestProject relative to the supplied source root.
        process = subprocess.run(
            [*lean_command, str(runner)],
            cwd=source_root,
            env=env,
            text=True,
            stdout=subprocess.PIPE,
            stderr=subprocess.STDOUT,
            check=False,
        )
        if process.returncode != 0:
            raise ValueError(
                "Lean theorem elaboration failed:\n" + process.stdout.rstrip()
            )


def main() -> int:
    parser = argparse.ArgumentParser(
        description="Produce a locally Lean-checked James/DASHI execution receipt."
    )
    parser.add_argument("--source-root", type=pathlib.Path, required=True)
    parser.add_argument("--module", required=True)
    parser.add_argument("--theorem", required=True)
    parser.add_argument(
        "--verdict",
        choices=("certified_holds", "certified_refuted"),
        required=True,
    )
    parser.add_argument("--graph", type=pathlib.Path, required=True)
    parser.add_argument("--output", type=pathlib.Path, required=True)
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
    parser.add_argument(
        "--lean-command",
        help="Lean command prefix, e.g. 'lake env lean'; auto-detected when omitted",
    )
    parser.add_argument(
        "--reference",
        action="append",
        default=[],
        help="additional provenance reference; may be repeated",
    )
    args = parser.parse_args()

    try:
        source_root = args.source_root.resolve()
        if not source_root.is_dir():
            raise ValueError(f"source root is not a directory: {source_root}")
        if not args.graph.is_file():
            raise ValueError(f"canonical graph does not exist: {args.graph}")

        manifest_rows = load_manifest(args.manifest)
        verify_source_tree(source_root, manifest_rows)

        polarity = "positive" if args.verdict == "certified_holds" else "negative"
        contracts = load_contracts(args.contracts)
        contract_key = (args.module, args.theorem, polarity)
        if contract_key not in contracts:
            raise ValueError(
                "requested theorem/verdict is not pinned in BRIDGE_CONTRACTS.tsv: "
                f"{contract_key!r}"
            )

        manifest_modules = {row["module"] for row in manifest_rows}
        if args.module not in manifest_modules:
            raise ValueError(f"module is absent from pinned source manifest: {args.module}")

        lean_command = resolve_lean_command(source_root, args.lean_command)
        check_theorem(source_root, args.module, args.theorem, lean_command)

        receipt = {
            "contract": CONTRACT,
            "request_id": REQUEST_ID,
            "source_archive_sha256": ARCHIVE_SHA256,
            "module": args.module,
            "theorem": args.theorem,
            "input_graph_sha256": sha256(args.graph),
            "verdict": args.verdict,
            "references": [
                str(args.graph),
                f"RequestProject/{args.module}.lean",
                *args.reference,
            ],
        }
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(
            json.dumps(receipt, indent=2, sort_keys=False) + "\n",
            encoding="utf-8",
        )

    except (OSError, ValueError, KeyError, subprocess.SubprocessError) as exc:
        print(f"James/DASHI receipt production FAILED: {exc}", file=sys.stderr)
        return 1

    print(
        "James/DASHI execution receipt produced: "
        f"{args.module}::{args.theorem} {args.verdict} -> {args.output}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
