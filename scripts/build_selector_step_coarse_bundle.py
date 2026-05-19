#!/usr/bin/env python3
"""Build a repo-native selector commutation bundle from the current Agda-backed moonshine adapter."""

from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any

from check_selector_step_coarse import compare_reports
from moonshine_prime_from_twined_trace_shift import (
    SOURCE_PATH,
    build_state,
    extract_orientation_prime,
)


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--constructor",
        choices=("identity", "nontrivial"),
        default="identity",
        help="Which exported shift trace constructor to anchor provenance on",
    )
    parser.add_argument(
        "--check",
        action="store_true",
        help="Also run the selector commutation comparison and embed the report",
    )
    parser.add_argument("--output", help="Optional path for the bundle JSON")
    parser.add_argument("--pretty", action="store_true", help="Pretty-print JSON output")
    return parser.parse_args()


def build_bundle(*, constructor: str, with_check: bool) -> dict[str, Any]:
    source_text = SOURCE_PATH.read_text()
    orientation_prime = extract_orientation_prime(source_text, constructor)
    state = build_state(orientation_prime=orientation_prime, constructor=constructor)

    bundle: dict[str, Any] = {
        "coarse_step": state,
        "step_coarse": state,
        "provenance": {
            "adapter": "build_selector_step_coarse_bundle",
            "source_adapter": "moonshine_prime_from_twined_trace_shift",
            "source_module": str(SOURCE_PATH),
            "source_constructor": constructor,
            "orientation_prime": orientation_prime,
            "interpretation": "bridge_aligned_transport_bundle",
            "note": (
                "This bundle reuses the current Agda-backed transported moonshine state "
                "on both sides. It is a cheap bridge-aligned runtime probe, not an "
                "independent evaluator of shiftCoarse and shiftStep."
            ),
        },
    }
    if with_check:
        bundle["comparison"] = compare_reports(bundle["coarse_step"], bundle["step_coarse"])
    return bundle


def main() -> int:
    args = parse_args()
    bundle = build_bundle(constructor=args.constructor, with_check=args.check)
    text = json.dumps(bundle, indent=2 if args.pretty else None, sort_keys=True)
    if args.output:
        Path(args.output).write_text(text + ("\n" if args.pretty else ""))
    else:
        print(text)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
