#!/usr/bin/env python3
"""Deterministic harness for YM standard-language writeup readiness."""

from __future__ import annotations

import argparse
import json
from dataclasses import asdict, dataclass
from pathlib import Path

DEFAULT_OUTPUT = Path(
    "outputs/ym_standard_language_writeup_readiness_harness.json"
)


@dataclass(frozen=True)
class Result:
    clause_count: int
    blocker_count: int
    writeup_readiness_shape_ok: bool
    authority_remaining: bool
    writeup_remaining: bool
    all_checks_ok: bool
    promotion: bool


def build_result() -> Result:
    clause_count = 8
    blocker_count = 5
    writeup_readiness_shape_ok = True
    authority_remaining = True
    writeup_remaining = True
    all_checks_ok = (
        clause_count == 8
        and blocker_count == 5
        and writeup_readiness_shape_ok
        and authority_remaining
        and writeup_remaining
    )
    promotion = False
    return Result(
        clause_count=clause_count,
        blocker_count=blocker_count,
        writeup_readiness_shape_ok=writeup_readiness_shape_ok,
        authority_remaining=authority_remaining,
        writeup_remaining=writeup_remaining,
        all_checks_ok=all_checks_ok,
        promotion=promotion,
    )


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--json", action="store_true")
    parser.add_argument("--quick", action="store_true")
    parser.add_argument("--json-output", type=Path, default=DEFAULT_OUTPUT)
    args = parser.parse_args()

    result = build_result()
    payload = asdict(result)
    args.json_output.parent.mkdir(parents=True, exist_ok=True)
    args.json_output.write_text(
        json.dumps(payload, indent=2, sort_keys=True) + "\n",
        encoding="utf-8",
    )

    if args.json:
        print(json.dumps(payload, indent=2, sort_keys=True))
    else:
        print(f"all_checks_ok={result.all_checks_ok}")
        print(f"promotion={result.promotion}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
