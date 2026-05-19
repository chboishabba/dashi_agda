#!/usr/bin/env python3
"""Cheap carrier-level check for the canonical 15 Monster/Ogg primes."""

from __future__ import annotations

import argparse
import json
from pathlib import Path

from moonshine_prime_object import SSP_PRIMES

CANONICAL_MONSTER_PRIMES = [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 41, 47, 59, 71]


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--source-json",
        help=(
            "Optional JSON file carrying a prime-keyed object under one of "
            "'signature', 'factorVector', or 'carrier'."
        ),
    )
    parser.add_argument(
        "--pretty",
        action="store_true",
        help="Pretty-print the JSON result.",
    )
    return parser.parse_args()


def read_source_keys(path: Path) -> list[int] | None:
    payload = json.loads(path.read_text())
    for key in ("signature", "factorVector", "carrier"):
        raw = payload.get(key)
        if isinstance(raw, dict):
            return sorted(int(k) for k in raw)
        if key == "carrier" and isinstance(raw, list):
            return [int(v) for v in raw]
    return None


def main() -> int:
    args = parse_args()
    source_keys = read_source_keys(Path(args.source_json)) if args.source_json else None
    result = {
        "ssp_primes": SSP_PRIMES,
        "canonical_monster_primes": CANONICAL_MONSTER_PRIMES,
        "ssp_equals_canonical": SSP_PRIMES == CANONICAL_MONSTER_PRIMES,
        "source_keys": source_keys,
        "source_equals_canonical": (
            source_keys == CANONICAL_MONSTER_PRIMES if source_keys is not None else None
        ),
    }
    print(json.dumps(result, indent=2 if args.pretty else None, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
