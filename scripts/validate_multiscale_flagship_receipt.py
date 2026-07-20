#!/usr/bin/env python3
"""Validate a DASHI flagship benchmark receipt.

This is a governance gate, not a benchmark implementation. It fails closed unless
one selected flagship supplies exactness, baseline, quality, resource, ablation,
and leakage receipts in a machine-readable JSON document.
"""

from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path
from typing import Any

REQUIRED_BOOL_TRUE = (
    "exact_roundtrip",
    "held_out_evaluation",
    "baseline_declared",
    "quality_metric_declared",
    "runtime_measured",
    "memory_measured",
    "side_information_accounted",
    "no_test_leakage",
)

REQUIRED_ABLATIONS = (
    "multiscale_prediction",
    "ultrametric_context",
    "symmetry_quotient",
    "temporal_or_transport_residual",
)

VALID_FLAGSHIPS = {"triadic_video_codec", "observer_wave_transport", "sparse_vorticity"}


def _is_number(value: Any) -> bool:
    return isinstance(value, (int, float)) and not isinstance(value, bool)


def validate(receipt: dict[str, Any]) -> list[str]:
    errors: list[str] = []

    flagship = receipt.get("flagship")
    if flagship not in VALID_FLAGSHIPS:
        errors.append(f"flagship must be one of {sorted(VALID_FLAGSHIPS)}")

    for key in REQUIRED_BOOL_TRUE:
        if receipt.get(key) is not True:
            errors.append(f"{key} must be true")

    quality = receipt.get("quality")
    if not isinstance(quality, dict):
        errors.append("quality must be an object")
    else:
        for key in ("candidate", "baseline"):
            if not _is_number(quality.get(key)):
                errors.append(f"quality.{key} must be numeric")
        if quality.get("direction") not in {"higher_is_better", "lower_is_better"}:
            errors.append("quality.direction must be higher_is_better or lower_is_better")

    resources = receipt.get("resources")
    if not isinstance(resources, dict):
        errors.append("resources must be an object")
    else:
        for metric in ("runtime_seconds", "peak_memory_bytes"):
            block = resources.get(metric)
            if not isinstance(block, dict):
                errors.append(f"resources.{metric} must be an object")
                continue
            for key in ("candidate", "baseline"):
                if not _is_number(block.get(key)) or block[key] < 0:
                    errors.append(f"resources.{metric}.{key} must be non-negative numeric")

    ablations = receipt.get("ablations")
    if not isinstance(ablations, dict):
        errors.append("ablations must be an object")
    else:
        for name in REQUIRED_ABLATIONS:
            block = ablations.get(name)
            if not isinstance(block, dict):
                errors.append(f"ablations.{name} must be an object")
                continue
            if block.get("run") is not True:
                errors.append(f"ablations.{name}.run must be true")
            if not _is_number(block.get("quality")):
                errors.append(f"ablations.{name}.quality must be numeric")
            if not _is_number(block.get("runtime_seconds")):
                errors.append(f"ablations.{name}.runtime_seconds must be numeric")

    claims = receipt.get("claims", {})
    if claims.get("universal_superiority") is True:
        errors.append("universal_superiority must not be promoted by one flagship receipt")
    if claims.get("shannon_optimality") is True and receipt.get("coding_theorem_proved") is not True:
        errors.append("shannon_optimality requires coding_theorem_proved=true")
    if claims.get("continuum_physics") is True and receipt.get("continuum_theorem_proved") is not True:
        errors.append("continuum_physics requires continuum_theorem_proved=true")

    return errors


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("receipt", type=Path)
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()

    try:
        data = json.loads(args.receipt.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError) as exc:
        print(json.dumps({"passed": False, "errors": [str(exc)]}, indent=2))
        return 2

    errors = validate(data)
    result = {
        "passed": not errors,
        "flagship": data.get("flagship"),
        "errors": errors,
    }
    rendered = json.dumps(result, indent=2, sort_keys=True)
    print(rendered)
    if args.output:
        args.output.write_text(rendered + "\n", encoding="utf-8")
    return 0 if not errors else 1


if __name__ == "__main__":
    sys.exit(main())
