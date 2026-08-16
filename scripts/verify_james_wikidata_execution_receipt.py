#!/usr/bin/env python3
from __future__ import annotations

import argparse
import csv
import hashlib
import json
import pathlib
import sys
from typing import Any

REQUEST_ID = "ae06ae06-2580-422a-8fc3-92aeaaca8762"
ARCHIVE_SHA256 = "d394cd224742dea06a47d2cc6c150e9284e2d6ea291a02c3ba2b2dd04d4f5f88"
CONTRACT = "dashi.james_wikidata_execution.v1"
VERDICTS = {"certified_holds", "certified_refuted"}


def sha256(path: pathlib.Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as handle:
        for chunk in iter(lambda: handle.read(1 << 20), b""):
            digest.update(chunk)
    return digest.hexdigest()


def required_text(row: dict[str, Any], key: str) -> str:
    value = row.get(key)
    if not isinstance(value, str) or not value.strip():
        raise ValueError(f"{key} must be a non-empty string")
    return value.strip()


def load_contracts(path: pathlib.Path) -> set[tuple[str, str, str]]:
    with path.open(encoding="utf-8", newline="") as handle:
        return {
            (row["module"], row["theorem"], row["polarity"])
            for row in csv.DictReader(handle, delimiter="\t")
        }


def main() -> int:
    parser = argparse.ArgumentParser(
        description="Verify a content-addressed James/DASHI theorem execution receipt."
    )
    parser.add_argument("receipt", type=pathlib.Path)
    parser.add_argument("graph", type=pathlib.Path, help="canonical graph TSV used by the receipt")
    parser.add_argument(
        "--contracts",
        type=pathlib.Path,
        default=pathlib.Path("third_party/jmdupont_wikidata_lean/BRIDGE_CONTRACTS.tsv"),
    )
    args = parser.parse_args()

    try:
        raw = json.loads(args.receipt.read_text(encoding="utf-8"))
        if not isinstance(raw, dict):
            raise ValueError("receipt root must be an object")
        if raw.get("contract") != CONTRACT:
            raise ValueError(f"unsupported contract {raw.get('contract')!r}")

        request_id = required_text(raw, "request_id")
        archive_hash = required_text(raw, "source_archive_sha256")
        module = required_text(raw, "module")
        theorem = required_text(raw, "theorem")
        graph_hash = required_text(raw, "input_graph_sha256")
        verdict = required_text(raw, "verdict")
        if verdict not in VERDICTS:
            raise ValueError(f"verdict must be one of {sorted(VERDICTS)}")

        if request_id != REQUEST_ID:
            raise ValueError("Aristotle request id does not match pinned source")
        if archive_hash != ARCHIVE_SHA256:
            raise ValueError("source archive hash does not match pinned source")

        actual_graph_hash = sha256(args.graph)
        if graph_hash != actual_graph_hash:
            raise ValueError(
                f"input graph hash mismatch: receipt {graph_hash}, actual {actual_graph_hash}"
            )

        expected_polarity = "positive" if verdict == "certified_holds" else "negative"
        contracts = load_contracts(args.contracts)
        if (module, theorem, expected_polarity) not in contracts:
            raise ValueError(
                "theorem/verdict pair is not pinned in BRIDGE_CONTRACTS.tsv "
                f"as {expected_polarity}"
            )

        refs = raw.get("references", [])
        if not isinstance(refs, list) or not all(isinstance(ref, str) and ref for ref in refs):
            raise ValueError("references must be a list of non-empty strings")

    except (OSError, json.JSONDecodeError, ValueError, KeyError) as exc:
        print(f"James/DASHI execution receipt FAILED: {exc}", file=sys.stderr)
        return 1

    print(
        "James/DASHI execution receipt OK: "
        f"{module}::{theorem} {verdict}, graph={graph_hash}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
