#!/usr/bin/env python3
"""Cheap selector commutation probe for coarse(step(x)) vs step(coarse(x))."""

from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any

from check_canonical_prime_concentration import concentration_report
from select_canonical_prime import select_from_report


def load_payload(path: str) -> dict[str, Any]:
    return json.loads(Path(path).read_text())


def pair_payloads(args: argparse.Namespace) -> tuple[dict[str, Any], dict[str, Any]]:
    if args.bundle:
        payload = load_payload(args.bundle)
        try:
            lhs = payload["coarse_step"]
            rhs = payload["step_coarse"]
        except KeyError as exc:
            raise SystemExit(
                f"bundle JSON must contain 'coarse_step' and 'step_coarse'; missing {exc.args[0]!r}"
            ) from exc
        return lhs, rhs

    if not args.coarse_step or not args.step_coarse:
        raise SystemExit("pass either --bundle or both --coarse-step and --step-coarse")

    return load_payload(args.coarse_step), load_payload(args.step_coarse)


def selector_report(payload: dict[str, Any]) -> dict[str, Any]:
    return select_from_report(concentration_report(payload))


def compare_reports(lhs: dict[str, Any], rhs: dict[str, Any]) -> dict[str, Any]:
    lhs_sel = selector_report(lhs)
    rhs_sel = selector_report(rhs)

    return {
        "selector_commutes": lhs_sel["selected_prime"] == rhs_sel["selected_prime"],
        "weight_commutes": lhs_sel["selected_weight"] == rhs_sel["selected_weight"],
        "lhs": {
            "selected_prime": lhs_sel["selected_prime"],
            "selected_weight": lhs_sel["selected_weight"],
            "dominant_primes": lhs_sel["dominant_primes"],
            "tie_count": lhs_sel["tie_count"],
            "basin_label": lhs_sel["basin_label"],
            "mdl_denominator": lhs_sel["mdl_denominator"],
        },
        "rhs": {
            "selected_prime": rhs_sel["selected_prime"],
            "selected_weight": rhs_sel["selected_weight"],
            "dominant_primes": rhs_sel["dominant_primes"],
            "tie_count": rhs_sel["tie_count"],
            "basin_label": rhs_sel["basin_label"],
            "mdl_denominator": rhs_sel["mdl_denominator"],
        },
    }


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--bundle", help="JSON file with keys 'coarse_step' and 'step_coarse'")
    parser.add_argument("--coarse-step", help="MoonshinePrimeState JSON for coarse(step(x))")
    parser.add_argument("--step-coarse", help="MoonshinePrimeState JSON for step(coarse(x))")
    parser.add_argument("--pretty", action="store_true", help="Pretty-print JSON")
    return parser.parse_args()


def main() -> int:
    args = parse_args()
    lhs, rhs = pair_payloads(args)
    report = compare_reports(lhs, rhs)
    print(json.dumps(report, indent=2 if args.pretty else None, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
