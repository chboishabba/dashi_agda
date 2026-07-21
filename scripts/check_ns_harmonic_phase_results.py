#!/usr/bin/env python3
"""Semantic checks for multiplier, full-operator and near-triad finite receipts."""
from __future__ import annotations

import argparse
import hashlib
import json
from fractions import Fraction
from pathlib import Path
from typing import Any


def digest(payload: Any) -> str:
    return hashlib.sha256(json.dumps(payload, sort_keys=True, separators=(",", ":")).encode()).hexdigest()


def load_checked(path: Path) -> tuple[dict[str, Any], bool]:
    payload = json.loads(path.read_text(encoding="utf-8"))
    supplied = payload.pop("sha256", None)
    return payload, supplied == digest(payload)


def frac(text: str) -> Fraction:
    return Fraction(text)


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("--multiplier-json", type=Path, required=True)
    ap.add_argument("--full-operator-json", type=Path, required=True)
    ap.add_argument("--near-json", type=Path, required=True)
    ap.add_argument("--output-json", type=Path, required=True)
    args = ap.parse_args()

    multiplier, multiplier_digest = load_checked(args.multiplier_json)
    full_operator, full_operator_digest = load_checked(args.full_operator_json)
    near, near_digest = load_checked(args.near_json)

    checks = {
        "multiplier_digest": multiplier_digest,
        "full_operator_digest": full_operator_digest,
        "near_digest": near_digest,
        "multiplier_scale_invariant": multiplier["all_rows_scale_invariant"] is True,
        "multiplier_R8_exact": multiplier["R8_symbolic_gain"] == "1/128",
        "multiplier_promotions_false": all(value is False for value in multiplier["promotion"].values()),
        "full_operator_promotions_false": all(value is False for value in full_operator["promotion"].values()),
        "full_operator_does_not_fit_one_eighth_in_test_norm": frac(full_operator["schur_product"]) > Fraction(1, 8),
        "near_candidates_are_one": near["integer_candidate_constants"] == {"LH": 1, "HL": 1, "HH": 1},
        "near_promotions_false": all(value is False for value in near["promotion"].values()),
        "near_cutoff_rows_present": [row["cutoff"] for row in near["rows"]] == [2, 3],
    }
    errors = [name for name, ok in checks.items() if not ok]
    out = {
        "schema": "check_ns_harmonic_phase_results.v1",
        "checks": checks,
        "error_count": len(errors),
        "errors": errors,
        "ok": not errors,
    }
    args.output_json.parent.mkdir(parents=True, exist_ok=True)
    args.output_json.write_text(json.dumps(out, sort_keys=True, indent=2) + "\n", encoding="utf-8")
    print(json.dumps(out, sort_keys=True, indent=2))
    if errors:
        raise SystemExit(1)


if __name__ == "__main__":
    main()
