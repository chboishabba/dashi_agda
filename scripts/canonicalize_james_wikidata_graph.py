#!/usr/bin/env python3
from __future__ import annotations

import argparse
import hashlib
import json
import pathlib
import sys
from typing import Any

KINDS = ("item", "level", "p279", "p31", "disjoint")


def _text(value: Any, *, where: str) -> str:
    if not isinstance(value, str) or not value or "\t" in value or "\n" in value:
        raise ValueError(f"{where} must be a non-empty single-line string")
    return value


def _pair(value: Any, *, where: str) -> tuple[str, str]:
    if not isinstance(value, list) or len(value) != 2:
        raise ValueError(f"{where} must be a two-element list")
    return (_text(value[0], where=f"{where}[0]"), _text(value[1], where=f"{where}[1]"))


def canonical_lines(payload: dict[str, Any]) -> list[str]:
    name = _text(payload.get("name"), where="name")
    unknown = set(payload) - {"name", *KINDS}
    if unknown:
        raise ValueError(f"unknown graph keys: {', '.join(sorted(unknown))}")

    lines = [f"name\t{name}"]

    items = payload.get("item", [])
    if not isinstance(items, list):
        raise ValueError("item must be a list")
    for item in sorted({_text(value, where="item[]") for value in items}):
        lines.append(f"item\t{item}")

    for kind in ("level", "p279", "p31", "disjoint"):
        raw = payload.get(kind, [])
        if not isinstance(raw, list):
            raise ValueError(f"{kind} must be a list")
        pairs = sorted({_pair(value, where=f"{kind}[]") for value in raw})
        for left, right in pairs:
            lines.append(f"{kind}\t{left}\t{right}")

    return lines


def canonical_bytes(payload: dict[str, Any]) -> bytes:
    return ("\n".join(canonical_lines(payload)) + "\n").encode("utf-8")


def main() -> int:
    parser = argparse.ArgumentParser(
        description="Canonicalize a concrete QID/P31/P279 Wikidata fragment for the James/DASHI bridge."
    )
    parser.add_argument("input", type=pathlib.Path, help="input JSON graph")
    parser.add_argument("--output", type=pathlib.Path, help="canonical TSV output")
    parser.add_argument("--receipt", type=pathlib.Path, help="optional graph identity receipt JSON")
    args = parser.parse_args()

    try:
        payload = json.loads(args.input.read_text(encoding="utf-8"))
        if not isinstance(payload, dict):
            raise ValueError("input root must be an object")
        rendered = canonical_bytes(payload)
    except (OSError, json.JSONDecodeError, ValueError) as exc:
        print(f"canonicalization failed: {exc}", file=sys.stderr)
        return 1

    digest = hashlib.sha256(rendered).hexdigest()
    if args.output:
        args.output.write_bytes(rendered)
    else:
        sys.stdout.buffer.write(rendered)

    if args.receipt:
        receipt = {
            "contract": "dashi.james_wikidata_graph.v1",
            "graph_name": payload["name"],
            "sha256": digest,
            "canonicalization": "sorted-unique-tsv-v1",
            "counts": {
                kind: len({tuple(x) if isinstance(x, list) else x for x in payload.get(kind, [])})
                for kind in KINDS
            },
        }
        args.receipt.write_text(json.dumps(receipt, indent=2, sort_keys=True) + "\n", encoding="utf-8")

    print(f"sha256={digest}", file=sys.stderr)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
