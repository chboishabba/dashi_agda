#!/usr/bin/env python3
"""Validate the deterministic concrete periodic proof-program receipt."""
from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
from typing import Any

SCHEMA = "ns_periodic_concrete_proof_program.v1"


def digest(payload: Any) -> str:
    raw = json.dumps(payload, sort_keys=True, separators=(",", ":")).encode("utf-8")
    return hashlib.sha256(raw).hexdigest()


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("--source-json", type=Path, required=True)
    ap.add_argument("--output-json", type=Path, required=True)
    args = ap.parse_args()

    payload = json.loads(args.source_json.read_text(encoding="utf-8"))
    supplied = payload.pop("certificate_sha256", None)
    checks = {
        "schema": payload.get("schema") == SCHEMA,
        "digest": supplied == digest(payload),
        "far_low_enumeration": payload["far_low"]["small_core"]["enumeration_below_analytic"] is True,
        "far_low_R8": payload["far_low"]["certificate"]["normalized_total"] == "1/128" and payload["far_low"]["certificate"]["fits_one_eighth"] is True,
        "far_high_R8": payload["far_high"]["R8_total"] == "1/16" and payload["far_high"]["R8_fits_one_eighth"] is True,
        "near_budget": payload["near_triad"]["candidate_budget_viable"] is True and payload["near_triad"]["optimized_residual_total"] == "64",
        "five_halves_counterexample": payload["five_halves"]["unconditional_or_static_compact_gamma_adjacent_contraction_refuted"] is True,
        "boundary_falsifier_active": payload["boundary_faces"]["all_candidate_ledgers_positive"] is False,
        "coverage_diffuse_case": payload["coverage"]["families"]["plateau_8"]["diffuse_branch"] is True,
        "coverage_hysteresis": payload["coverage"]["hysteresis_trace"]["switch_count"] == 1,
        "all_promotions_false": all(value is False for value in payload["promotion"].values()),
        "five_halves_not_promoted": payload["five_halves"]["pointwise_five_halves_promoted"] is False,
        "dini_not_promoted": payload["boundary_faces"]["dini_inwardness_promoted"] is False,
        "coverage_not_promoted": payload["coverage"]["all_data_coverage_promoted"] is False,
    }
    errors = [name for name, ok in checks.items() if not ok]
    out = {"schema": "check_ns_periodic_concrete_proof_program.v1", "checks": checks, "error_count": len(errors), "errors": errors, "ok": not errors}
    args.output_json.parent.mkdir(parents=True, exist_ok=True)
    args.output_json.write_text(json.dumps(out, sort_keys=True, indent=2) + "\n", encoding="utf-8")
    print(json.dumps(out, sort_keys=True, indent=2))
    if errors:
        raise SystemExit(1)


if __name__ == "__main__":
    main()
