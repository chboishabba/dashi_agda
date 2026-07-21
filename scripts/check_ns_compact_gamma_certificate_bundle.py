#!/usr/bin/env python3
from __future__ import annotations

import argparse
import hashlib
import json
from fractions import Fraction
from pathlib import Path
from typing import Any

SCHEMA = "ns_compact_gamma_certificate_bundle.v1"


def parse_q(text: str) -> Fraction:
    return Fraction(text)


def digest(payload: Any) -> str:
    raw = json.dumps(payload, sort_keys=True, separators=(",", ":")).encode()
    return hashlib.sha256(raw).hexdigest()


def check(payload: dict[str, Any]) -> dict[str, Any]:
    errors: list[str] = []
    if payload.get("schema") != SCHEMA:
        errors.append("schema_mismatch")
    stored = payload.get("certificate_sha256")
    unsigned = dict(payload)
    unsigned.pop("certificate_sha256", None)
    if stored != digest(unsigned):
        errors.append("certificate_digest_mismatch")
    if payload.get("authority") != "exact_finite_core_plus_unproved_analytic_tail_obligations":
        errors.append("authority_mismatch")
    promotion = payload.get("promotion", {})
    for key in ("agda_inhabitant", "full_ns", "clay"):
        if promotion.get(key) is not False:
            errors.append(f"promotion_flag_not_false:{key}")
    leaves = payload.get("leaves", {})
    required = ("adjacent_shell", "near_triad", "far_low", "far_high", "official_coverage")
    for name in required:
        if name not in leaves:
            errors.append(f"missing_leaf:{name}")
    adjacent = leaves.get("adjacent_shell", {})
    if adjacent.get("unconditional_contraction_refuted") is not True:
        errors.append("adjacent_unconditional_refutation_missing")
    near = leaves.get("near_triad", {})
    if near.get("oddness_exact") is not True:
        errors.append("near_oddness_not_exact")
    if near.get("signed_coercivity_refuted_on_core") is not True:
        errors.append("near_signed_refutation_missing")
    if near.get("finite_core_absorption_verified") is not True:
        errors.append("near_core_absorption_not_verified")
    if parse_q(near.get("delta", "-1")) <= 0:
        errors.append("near_delta_not_positive")
    low = leaves.get("far_low", {})
    if low.get("fits_one_eighth_budget") is not True:
        errors.append("far_low_budget_failed")
    if parse_q(low.get("normalized_radius_gain", "1")) > Fraction(1, 8):
        errors.append("far_low_exact_budget_failed")
    high = leaves.get("far_high", {})
    if high.get("fits_one_eighth_budget") is not True:
        errors.append("far_high_budget_failed")
    if parse_q(high.get("geometric_tail_majorant", "1")) > Fraction(1, 8):
        errors.append("far_high_exact_budget_failed")
    coverage = leaves.get("official_coverage", {})
    if coverage.get("fixed_absolute_floor_route_rejected") is not True:
        errors.append("coverage_scaling_obstruction_missing")
    for name in required:
        obligation = leaves.get(name, {}).get("required_tail_obligation")
        if not isinstance(obligation, dict) or not obligation.get("name") or not obligation.get("statement"):
            errors.append(f"tail_obligation_missing:{name}")
    return {
        "schema": "check_ns_compact_gamma_certificate_bundle.v1",
        "source_schema": payload.get("schema"),
        "source_certificate_sha256": stored,
        "error_count": len(errors),
        "errors": errors,
        "ok": not errors,
        "theorem_promoted": False,
        "full_ns_promoted": False,
        "clay_promoted": False,
    }


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("--source-json", type=Path, required=True)
    ap.add_argument("--output-json", type=Path, required=True)
    args = ap.parse_args()
    payload = json.loads(args.source_json.read_text(encoding="utf-8"))
    result = check(payload)
    args.output_json.parent.mkdir(parents=True, exist_ok=True)
    text = json.dumps(result, sort_keys=True, indent=2) + "\n"
    args.output_json.write_text(text, encoding="utf-8")
    print(text, end="")
    raise SystemExit(0 if result["ok"] else 1)


if __name__ == "__main__":
    main()
