#!/usr/bin/env python3
"""Audit weighted Schur constants on coarse shell/angle transfer receipts.

The input is produced by ``ns_triad_gamma_gap_raw_hat_export.py --aggregate-only``.
For each checkpoint we form the finite nonnegative matrix

    K[p, (q, angle)] = gross_activity_fraction(p, q, angle)

and evaluate the weighted row and column constants

    C_R = max_p sum_t K[p,t] w_T(t) / w_S(p)
    C_C = max_t sum_p K[p,t] w_S(p) / w_T(t).

This is a discovery diagnostic for choosing plausible shell weights.  It is not
the repository's concrete rectangular pair-incidence kernel, does not prove the
weighted Schur theorem in ``ns_plan.txt``, and does not determine ``C_err``.
"""

from __future__ import annotations

import argparse
import json
import math
from pathlib import Path
from typing import Any

import numpy as np


SCRIPT_NAME = "scripts/ns_shell_angle_weighted_schur_audit.py"


def parse_float_list(raw: str) -> tuple[float, ...]:
    values = tuple(sorted({float(token.strip()) for token in raw.split(",") if token.strip()}))
    if not values or any(not math.isfinite(value) or value < 0.0 for value in values):
        raise ValueError("weight exponents must be finite and nonnegative")
    return values


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--input-json", type=Path, required=True)
    parser.add_argument("--output-json", type=Path, required=True)
    parser.add_argument("--source-exponents", default="0,0.25,0.5,1,2")
    parser.add_argument("--target-exponents", default="0,0.25,0.5,1,2")
    parser.add_argument("--pretty", action="store_true")
    return parser.parse_args()


def _receipts(payload: dict[str, Any]) -> list[dict[str, Any]]:
    for key in ("export_receipts", "receipts"):
        value = payload.get(key)
        if isinstance(value, list):
            return [row for row in value if isinstance(row, dict)]
    raise ValueError("input JSON has no export_receipts or receipts list")


def build_coarse_kernel(groups: list[dict[str, Any]]) -> tuple[list[int], list[tuple[int, int]], np.ndarray]:
    valid: list[tuple[int, int, int, float]] = []
    for group in groups:
        try:
            p = int(group["p_shell_offset"])
            q = int(group["q_shell_offset"])
            angle = int(group["angle_bin"])
            value = float(group.get("gross_activity_fraction", group["gross_activity"]))
        except (KeyError, TypeError, ValueError) as exc:
            raise ValueError(f"malformed coarse group: {group!r}") from exc
        if not math.isfinite(value) or value < 0.0:
            raise ValueError("coarse kernel entries must be finite and nonnegative")
        valid.append((p, q, angle, value))
    if not valid:
        raise ValueError("receipt contains no coarse shell/angle groups")

    rows = sorted({p for p, _q, _angle, _value in valid})
    columns = sorted({(q, angle) for _p, q, angle, _value in valid})
    row_index = {row: index for index, row in enumerate(rows)}
    column_index = {column: index for index, column in enumerate(columns)}
    kernel = np.zeros((len(rows), len(columns)), dtype=np.float64)
    for p, q, angle, value in valid:
        kernel[row_index[p], column_index[(q, angle)]] += value

    total = float(np.sum(kernel))
    if total <= 0.0:
        raise ValueError("coarse kernel has zero gross mass")
    # Old receipts may contain raw gross activity rather than fractions.  The
    # audit always works with a probability-mass kernel.
    kernel /= total
    return rows, columns, kernel


def shell_weight(offset: int, exponent: float) -> float:
    return float(2.0 ** (-float(exponent) * abs(int(offset))))


def weighted_schur_constants(
    rows: list[int],
    columns: list[tuple[int, int]],
    kernel: np.ndarray,
    source_exponent: float,
    target_exponent: float,
) -> dict[str, Any]:
    matrix = np.asarray(kernel, dtype=np.float64)
    if matrix.shape != (len(rows), len(columns)):
        raise ValueError("kernel shape does not match row/column carriers")
    if np.any(matrix < 0.0) or not np.all(np.isfinite(matrix)):
        raise ValueError("kernel must be finite and nonnegative")

    source_weights = np.asarray([shell_weight(row, source_exponent) for row in rows], dtype=np.float64)
    target_weights = np.asarray([shell_weight(column[0], target_exponent) for column in columns], dtype=np.float64)
    row_weighted_sums = matrix @ target_weights
    column_weighted_sums = matrix.T @ source_weights
    row_ratios = row_weighted_sums / source_weights
    column_ratios = column_weighted_sums / target_weights
    row_constant = float(np.max(row_ratios))
    column_constant = float(np.max(column_ratios))
    product_constant = row_constant * column_constant

    worst_row_index = int(np.argmax(row_ratios))
    worst_column_index = int(np.argmax(column_ratios))
    return {
        "source_exponent": float(source_exponent),
        "target_exponent": float(target_exponent),
        "row_constant": row_constant,
        "column_constant": column_constant,
        "product_constant": product_constant,
        "operator_constant_sqrt_product": float(math.sqrt(max(product_constant, 0.0))),
        "worst_row": {
            "p_shell_offset": int(rows[worst_row_index]),
            "weighted_sum": float(row_weighted_sums[worst_row_index]),
            "source_weight": float(source_weights[worst_row_index]),
            "ratio": float(row_ratios[worst_row_index]),
        },
        "worst_column": {
            "q_shell_offset": int(columns[worst_column_index][0]),
            "angle_bin": int(columns[worst_column_index][1]),
            "weighted_sum": float(column_weighted_sums[worst_column_index]),
            "target_weight": float(target_weights[worst_column_index]),
            "ratio": float(column_ratios[worst_column_index]),
        },
    }


def audit_receipt(
    receipt: dict[str, Any],
    source_exponents: tuple[float, ...],
    target_exponents: tuple[float, ...],
) -> dict[str, Any]:
    groups = receipt.get("coarse_shell_angle_groups")
    if not isinstance(groups, list):
        raise ValueError("receipt has no coarse_shell_angle_groups list")
    rows, columns, kernel = build_coarse_kernel([group for group in groups if isinstance(group, dict)])
    candidates = [
        weighted_schur_constants(rows, columns, kernel, source, target)
        for source in source_exponents
        for target in target_exponents
    ]
    candidates.sort(key=lambda row: (float(row["product_constant"]), float(row["row_constant"]), float(row["column_constant"])))
    signed = float(receipt.get("full_packet_signed_rate", 0.0))
    gross = float(receipt.get("full_packet_gross_activity", 0.0))
    return {
        "source_state": receipt.get("source_state"),
        "target_shell": receipt.get("target_shell"),
        "row_carrier_count": len(rows),
        "column_carrier_count": len(columns),
        "kernel_mass": float(np.sum(kernel)),
        "signed_to_gross_ratio": signed / gross if gross > 0.0 else None,
        "best_weight_candidate": candidates[0],
        "weight_candidates": candidates,
        "formal_pair_incidence_kernel_match_proved": False,
        "c_err_determined": False,
        "truth_authority": False,
        "theorem_authority": False,
        "clay_authority": False,
        "promoted": False,
    }


def minimax_summary(audits: list[dict[str, Any]]) -> dict[str, Any]:
    if not audits:
        raise ValueError("no audits available")
    parameter_pairs = [
        (float(candidate["source_exponent"]), float(candidate["target_exponent"]))
        for candidate in audits[0]["weight_candidates"]
    ]
    rows: list[dict[str, Any]] = []
    for source, target in parameter_pairs:
        matching = []
        for audit in audits:
            candidate = next(
                item for item in audit["weight_candidates"]
                if float(item["source_exponent"]) == source and float(item["target_exponent"]) == target
            )
            matching.append(candidate)
        rows.append(
            {
                "source_exponent": source,
                "target_exponent": target,
                "worst_row_constant": max(float(item["row_constant"]) for item in matching),
                "worst_column_constant": max(float(item["column_constant"]) for item in matching),
                "worst_product_constant": max(float(item["product_constant"]) for item in matching),
                "worst_operator_constant_sqrt_product": max(
                    float(item["operator_constant_sqrt_product"]) for item in matching
                ),
            }
        )
    rows.sort(key=lambda row: (float(row["worst_product_constant"]),
                               float(row["worst_row_constant"]),
                               float(row["worst_column_constant"])))
    return {
        "best_minimax_weight": rows[0],
        "weight_sweep": rows,
        "interpretation": (
            "Finite coarse transfer-mass diagnostic only.  The selected minimax weight is a candidate for the "
            "analytic shell weight; it is not a proof for the concrete rectangular incidence kernel."
        ),
    }


def main() -> None:
    args = parse_args()
    source_exponents = parse_float_list(args.source_exponents)
    target_exponents = parse_float_list(args.target_exponents)
    payload = json.loads(args.input_json.read_text(encoding="utf-8"))
    if not isinstance(payload, dict):
        raise ValueError("input JSON root must be an object")
    audits = [audit_receipt(receipt, source_exponents, target_exponents) for receipt in _receipts(payload)]
    output = {
        "schema_version": "1.0.0",
        "script": SCRIPT_NAME,
        "input_json": str(args.input_json),
        "authority": {
            "candidate_only": True,
            "empirical_non_promoting": True,
            "truth_authority": False,
            "theorem_authority": False,
            "clay_authority": False,
            "promoted": False,
        },
        "kernel_semantics": "normalized gross transfer mass on p-shell by (q-shell, angle-bin)",
        "formal_pair_incidence_kernel_match_proved": False,
        "audits": audits,
        "minimax": minimax_summary(audits),
        "limitations": [
            "coarse shell/angle projection loses mode-level incidence information",
            "empirical transfer mass is not the concrete Stage-3 rectangular kernel",
            "a product constant below any numerical threshold does not prove C_err < 4",
        ],
    }
    args.output_json.parent.mkdir(parents=True, exist_ok=True)
    args.output_json.write_text(json.dumps(output, indent=2 if args.pretty else None, sort_keys=True) + "\n",
                                encoding="utf-8")
    print(json.dumps({"output_json": str(args.output_json), "audit_count": len(audits)}, sort_keys=True))


if __name__ == "__main__":
    main()
