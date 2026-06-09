#!/usr/bin/env python3
"""Sprint 53 YM diameter-1/2 Wilson activity diagnostic.

This harness computes the p=7 diameter-1 and diameter-2 KP activity rows that
sit before the all-diameter Balaban/RG gate.  It deliberately emits both:

* the literal Wilson-defect activity |exp(-beta S_d) - 1|;
* the contour/action suppression envelope exp(a d - beta c_min d).

The local YM receipts use the contour/action envelope for KP suppression.  The
literal Wilson-defect diagnostic is included because it is the requested
carrier Wilson action check, but it does not decay to zero at large beta.
Nothing emitted here proves all-diameter KP, Balaban transfer, continuum YM, a
mass gap, or Clay Yang-Mills.
"""

from __future__ import annotations

import argparse
import csv
import json
import math
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import Any


DEFAULT_BETAS = (6.0, 7.69, 10.13, 13.64, 16.7)
PROMOTION_STATUS = "NO_PROMOTION_DIAGNOSTIC_ONLY"


@dataclass(frozen=True)
class DiameterKPActivityRow:
    beta: float
    p: int
    bt_branching_factor: int
    c_min: float
    entropy_a: float
    diameter1_action_lower_bound: float
    diameter2_action_lower_bound: float
    d1_literal_activity: float
    d2_literal_activity: float
    literal_ratio_d2_d1: float
    literal_q_empirical: float
    literal_branch_d1: float
    literal_same_prime_p_d1: float
    literal_branch_pass: int
    literal_same_prime_pass: int
    d1_unit_plaquette_literal_activity: float
    d2_unit_plaquette_literal_activity: float
    unit_plaquette_literal_branch_d1: float
    unit_plaquette_literal_branch_pass: int
    d1_unit_plaquette_suppressive_weight: float
    d2_unit_plaquette_suppressive_weight: float
    unit_plaquette_suppressive_branch_d1: float
    unit_plaquette_suppressive_branch_pass: int
    d1_contour_activity_bound: float
    d2_contour_activity_bound: float
    contour_ratio_d2_d1: float
    contour_q_empirical: float
    contour_branch_d1: float
    contour_same_prime_p_d1: float
    contour_branch_pass: int
    contour_same_prime_pass: int
    corrected_beta_threshold_same_prime_p: float
    bt_branch_beta_threshold: float
    beta_gap_to_same_prime_threshold: float
    beta_gap_to_bt_branch_threshold: float
    conditional_balaban_clearance: int
    finite_prefix_clearance: int
    all_diameter_certified: int
    balaban_rg_transfer_certified: int
    proof_gate_pass: int
    promotion_status: str
    interpretation: str


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--out-dir", type=Path, required=True)
    parser.add_argument("--betas", type=float, nargs="*", default=list(DEFAULT_BETAS))
    parser.add_argument("--p", type=int, default=7)
    parser.add_argument("--bt-branching-factor", type=int, default=None)
    parser.add_argument("--c-min", type=float, default=0.242)
    parser.add_argument("--entropy-a", type=float, default=0.5)
    parser.add_argument(
        "--balaban-carrier-beta",
        type=float,
        default=16.7,
        help="Carrier beta value treated as conditional until Balaban transfer is proved.",
    )
    parser.add_argument(
        "--all-diameter-certified",
        action="store_true",
        help="Mark all-diameter certificate supplied. Default is fail-closed false.",
    )
    parser.add_argument(
        "--balaban-rg-transfer-certified",
        action="store_true",
        help="Mark Balaban RG beta transfer supplied. Default is fail-closed false.",
    )
    return parser.parse_args()


def _safe_exp(x: float) -> float:
    try:
        return math.exp(x)
    except OverflowError:
        return math.inf


def _ratio(numer: float, denom: float) -> float:
    if denom == 0.0 or not math.isfinite(denom):
        return math.inf
    return numer / denom


def _literal_activity(beta: float, action_lower_bound: float) -> float:
    return abs(_safe_exp(-beta * action_lower_bound) - 1.0)


def _contour_activity(beta: float, c_min: float, entropy_a: float, diameter: int) -> float:
    return _safe_exp(entropy_a * diameter - beta * c_min * diameter)


def _threshold(branching: int, c_min: float, entropy_a: float) -> float:
    if branching <= 0 or c_min <= 0.0:
        return math.inf
    return (entropy_a + math.log(float(branching))) / c_min


def _interpret(row: DiameterKPActivityRow) -> str:
    if row.proof_gate_pass:
        return "PROOF_GATE_SUPPLIED_NO_CLAY_PROMOTION"
    if not row.literal_branch_pass and row.contour_branch_pass:
        return "LITERAL_WILSON_DEFECT_FAILS_CONTOUR_BOUND_CONDITIONALLY_PASSES"
    if row.contour_same_prime_pass and not row.contour_branch_pass:
        return "SAME_PRIME_P_CONTOUR_PASS_BT_BRANCHING_STILL_FAILS"
    if row.contour_branch_pass:
        return "CONTOUR_BOUND_FINITE_PREFIX_PASSES_CERTIFICATES_MISSING"
    return "FINITE_PREFIX_ACTIVITY_GATE_FAILS"


def _compute_rows(args: argparse.Namespace) -> list[DiameterKPActivityRow]:
    p = int(args.p)
    bt_branching = int(args.bt_branching_factor or (p + 1))
    same_prime_threshold = _threshold(p, args.c_min, args.entropy_a)
    bt_threshold = _threshold(bt_branching, args.c_min, args.entropy_a)
    rows: list[DiameterKPActivityRow] = []
    for beta in args.betas:
        d1_action = args.c_min
        d2_action = 2.0 * args.c_min
        d1_literal = _literal_activity(beta, d1_action)
        d2_literal = _literal_activity(beta, d2_action)
        literal_ratio = _ratio(d2_literal, d1_literal)
        d1_contour = _contour_activity(beta, args.c_min, args.entropy_a, 1)
        d2_contour = _contour_activity(beta, args.c_min, args.entropy_a, 2)
        contour_ratio = _ratio(d2_contour, d1_contour)

        literal_branch = bt_branching * d1_literal
        literal_same_prime = p * d1_literal
        contour_branch = bt_branching * d1_contour
        contour_same_prime = p * d1_contour
        literal_branch_pass = literal_branch < 1.0
        literal_same_prime_pass = literal_same_prime < 1.0
        d1_unit_literal = _literal_activity(beta, 1.0)
        d2_unit_literal = _literal_activity(beta, 2.0)
        unit_literal_branch = bt_branching * d1_unit_literal
        unit_literal_branch_pass = unit_literal_branch < 1.0
        d1_unit_weight = _safe_exp(-beta)
        d2_unit_weight = _safe_exp(-2.0 * beta)
        unit_weight_branch = bt_branching * d1_unit_weight
        unit_weight_branch_pass = unit_weight_branch < 1.0
        contour_branch_pass = contour_branch < 1.0
        contour_same_prime_pass = contour_same_prime < 1.0
        conditional_balaban = (
            beta >= args.balaban_carrier_beta
            and contour_branch_pass
            and args.balaban_rg_transfer_certified
        )
        finite_prefix = contour_ratio < 1.0 and contour_branch_pass
        proof_gate = (
            finite_prefix
            and args.all_diameter_certified
            and args.balaban_rg_transfer_certified
        )
        row = DiameterKPActivityRow(
            beta=beta,
            p=p,
            bt_branching_factor=bt_branching,
            c_min=args.c_min,
            entropy_a=args.entropy_a,
            diameter1_action_lower_bound=d1_action,
            diameter2_action_lower_bound=d2_action,
            d1_literal_activity=d1_literal,
            d2_literal_activity=d2_literal,
            literal_ratio_d2_d1=literal_ratio,
            literal_q_empirical=literal_ratio,
            literal_branch_d1=literal_branch,
            literal_same_prime_p_d1=literal_same_prime,
            literal_branch_pass=int(literal_branch_pass),
            literal_same_prime_pass=int(literal_same_prime_pass),
            d1_unit_plaquette_literal_activity=d1_unit_literal,
            d2_unit_plaquette_literal_activity=d2_unit_literal,
            unit_plaquette_literal_branch_d1=unit_literal_branch,
            unit_plaquette_literal_branch_pass=int(unit_literal_branch_pass),
            d1_unit_plaquette_suppressive_weight=d1_unit_weight,
            d2_unit_plaquette_suppressive_weight=d2_unit_weight,
            unit_plaquette_suppressive_branch_d1=unit_weight_branch,
            unit_plaquette_suppressive_branch_pass=int(unit_weight_branch_pass),
            d1_contour_activity_bound=d1_contour,
            d2_contour_activity_bound=d2_contour,
            contour_ratio_d2_d1=contour_ratio,
            contour_q_empirical=contour_ratio,
            contour_branch_d1=contour_branch,
            contour_same_prime_p_d1=contour_same_prime,
            contour_branch_pass=int(contour_branch_pass),
            contour_same_prime_pass=int(contour_same_prime_pass),
            corrected_beta_threshold_same_prime_p=same_prime_threshold,
            bt_branch_beta_threshold=bt_threshold,
            beta_gap_to_same_prime_threshold=same_prime_threshold - beta,
            beta_gap_to_bt_branch_threshold=bt_threshold - beta,
            conditional_balaban_clearance=int(conditional_balaban),
            finite_prefix_clearance=int(finite_prefix),
            all_diameter_certified=int(args.all_diameter_certified),
            balaban_rg_transfer_certified=int(args.balaban_rg_transfer_certified),
            proof_gate_pass=int(proof_gate),
            promotion_status=PROMOTION_STATUS,
            interpretation="",
        )
        rows.append(
            DiameterKPActivityRow(
                **{**asdict(row), "interpretation": _interpret(row)}
            )
        )
    return rows


def _jsonable(value: Any) -> Any:
    if isinstance(value, float) and not math.isfinite(value):
        if math.isnan(value):
            return "nan"
        return "inf" if value > 0 else "-inf"
    return value


def _write_csv(path: Path, rows: list[DiameterKPActivityRow]) -> None:
    fieldnames = list(DiameterKPActivityRow.__dataclass_fields__.keys())
    with path.open("w", newline="", encoding="utf-8") as handle:
        writer = csv.DictWriter(handle, fieldnames=fieldnames)
        writer.writeheader()
        for row in rows:
            writer.writerow(asdict(row))


def main() -> int:
    args = parse_args()
    args.out_dir.mkdir(parents=True, exist_ok=True)
    rows = _compute_rows(args)

    table_path = args.out_dir / "ym_diameter_kp_activity_table.csv"
    checks_path = args.out_dir / "ym_diameter_kp_activity_checks.json"
    manifest_path = args.out_dir / "ym_diameter_kp_activity_manifest.json"
    _write_csv(table_path, rows)

    best_contour = min((row.contour_branch_d1 for row in rows), default=math.inf)
    carrier_rows = [row for row in rows if abs(row.beta - args.balaban_carrier_beta) < 1e-9]
    carrier_row = carrier_rows[0] if carrier_rows else None
    checks = {
        "pass": bool(any(row.proof_gate_pass for row in rows)),
        "finite_prefix_rows_passing": int(sum(row.finite_prefix_clearance for row in rows)),
        "literal_branch_rows_passing": int(sum(row.literal_branch_pass for row in rows)),
        "unit_plaquette_literal_branch_rows_passing": int(
            sum(row.unit_plaquette_literal_branch_pass for row in rows)
        ),
        "unit_plaquette_suppressive_branch_rows_passing": int(
            sum(row.unit_plaquette_suppressive_branch_pass for row in rows)
        ),
        "contour_branch_rows_passing": int(sum(row.contour_branch_pass for row in rows)),
        "best_contour_branch_d1": _jsonable(best_contour),
        "carrier_beta": args.balaban_carrier_beta,
        "carrier_contour_branch_d1": _jsonable(
            carrier_row.contour_branch_d1 if carrier_row else math.inf
        ),
        "carrier_literal_branch_d1": _jsonable(
            carrier_row.literal_branch_d1 if carrier_row else math.inf
        ),
        "carrier_unit_plaquette_literal_branch_d1": _jsonable(
            carrier_row.unit_plaquette_literal_branch_d1 if carrier_row else math.inf
        ),
        "carrier_unit_plaquette_suppressive_branch_d1": _jsonable(
            carrier_row.unit_plaquette_suppressive_branch_d1 if carrier_row else math.inf
        ),
        "corrected_beta_threshold_same_prime_p": _jsonable(
            rows[0].corrected_beta_threshold_same_prime_p if rows else math.inf
        ),
        "bt_branch_beta_threshold": _jsonable(
            rows[0].bt_branch_beta_threshold if rows else math.inf
        ),
        "all_diameter_certified": bool(args.all_diameter_certified),
        "balaban_rg_transfer_certified": bool(args.balaban_rg_transfer_certified),
        "proof_gate_pass": bool(any(row.proof_gate_pass for row in rows)),
        "continuum_yang_mills_promoted": False,
        "clay_yang_mills_promoted": False,
        "promotion_status": PROMOTION_STATUS,
        "boundary": (
            "Sprint 53 computes diameter-1/2 literal Wilson-defect activity and "
            "the contour/action KP envelope. It is finite-prefix evidence only; "
            "all-diameter KP, Balaban transfer, continuum YM, mass gap, and Clay "
            "promotion remain unproved."
        ),
    }
    manifest = {
        "script": Path(__file__).name,
        "receipt_alignment": (
            "DASHI.Physics.Closure."
            "ClaySprintFiftyThreeYMDiameterOneKPReceipt"
        ),
        "outputs": {
            "table": str(table_path),
            "checks": str(checks_path),
            "manifest": str(manifest_path),
        },
        "defaults": {
            "betas": list(args.betas),
            "p": args.p,
            "bt_branching_factor": int(args.bt_branching_factor or (args.p + 1)),
            "c_min": args.c_min,
            "entropy_a": args.entropy_a,
            "balaban_carrier_beta": args.balaban_carrier_beta,
        },
        "promotion_status": PROMOTION_STATUS,
    }
    checks_path.write_text(
        json.dumps(checks, indent=2, default=_jsonable),
        encoding="utf-8",
    )
    manifest_path.write_text(json.dumps(manifest, indent=2), encoding="utf-8")
    print(
        f"wrote {table_path}, {checks_path}, {manifest_path}; "
        f"finite_prefix={checks['finite_prefix_rows_passing']} "
        f"proof_gate={checks['proof_gate_pass']} promotion={PROMOTION_STATUS}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
