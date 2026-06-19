#!/usr/bin/env python3
"""Materialize the deterministic Calc 12 result ledger from an existing selector artifact."""

from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path
from typing import Any


ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

import scripts.ns_clay_calc12_result_ledger as result_ledger


DEFAULT_INPUT = result_ledger.DEFAULT_INPUT
DEFAULT_OUTPUT = Path("scripts") / "data" / "outputs" / "ns_clay_calc12_result_ledger_real_N128_20260619.json"


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--input", type=Path, default=DEFAULT_INPUT, help="Path to the selector JSON.")
    parser.add_argument("--output", type=Path, default=DEFAULT_OUTPUT, help="Path to write the result ledger.")
    return parser.parse_args()


def read_json(path: Path) -> Any:
    return result_ledger.read_json(path)


def build_payload(input_payload: Any, *, input_path: Path) -> dict[str, Any]:
    payload = result_ledger.build_payload(input_payload, input_path=input_path)
    payload["validation_passed"] = result_ledger.validate_payload({**payload, "validation_passed": True})
    return payload


def validate_payload(payload: Any) -> bool:
    return result_ledger.validate_payload(payload)


def write_json(path: Path, value: Any) -> None:
    result_ledger.write_json(path, value)


def main() -> int:
    args = parse_args()
    try:
        input_payload = read_json(args.input)
        payload = build_payload(input_payload, input_path=args.input)
        if not validate_payload(payload):
            raise result_ledger.InputError("internal validation failed")
        write_json(args.output, payload)
    except result_ledger.InputError as exc:
        print(str(exc), file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
