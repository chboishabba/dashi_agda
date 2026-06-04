#!/usr/bin/env python3
"""Sprint 54 YM bare-vs-blocked KP transfer diagnostic.

This script makes the post-Sprint-53 scale distinction explicit:

* z_literal(beta) = |exp(-beta*S) - 1| is a Wilson-defect diagnostic and does
  not suppress at large beta;
* z_blocked(beta) = exp(a*d - beta*c_min*d) is the contour/action KP envelope;
* z_suppressive_unit(beta) = exp(-beta*d) is the unit-plaquette suppressive
  weight often confused with the literal defect.

The table is diagnostic only.  Passing blocked rows do not prove Balaban RG
scale transfer or all-diameter KP.
"""

from __future__ import annotations

import argparse
import csv
import json
import math
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import Any


DEFAULT_ROWS = (
    ("physical_bare", 6.0, 6.0),
    ("one_loop_carrier", 6.0, 7.69),
    ("kp_threshold", 6.0, 10.13),
    ("strict_seed", 6.0, 13.64),
    ("rg_flowed_carrier", 6.0, 16.7),
)
PROMOTION_STATUS = "NO_PROMOTION_DIAGNOSTIC_ONLY"


@dataclass(frozen=True)
class Sprint54YMScaleRow:
    label: str
    beta_bare: float
    beta_blocked: float
    p: int
    bt_branching_factor: int
    c_min: float
    entropy_a: float
    diameter: int
    z_literal_bare: float
    kp_literal_bare: float
    kp_passes_literal_bare: int
    z_literal_blocked: float
    kp_literal_blocked: float
    kp_passes_literal_blocked: int
    z_suppressive_unit_blocked: float
    kp_suppressive_unit_blocked: float
    kp_passes_suppressive_unit_blocked: int
    z_blocked_contour: float
    kp_blocked_contour: float
    kp_passes_blocked_contour: int
    z_blocked_contour_d2: float
    geometric_ratio_blocked_d2_d1: float
    combo_factor: int
    activity_ratio_q: float
    q_below_one: int
    weighted_kp_sum_ratio: float
    kp_sum_converges: int
    beta_needed_for_kp_sum: float
    beta_gap_to_kp_sum: float
    requires_rg_transfer: int
    finite_prefix_conditionally_clears: int
    all_diameter_certified: int
    balaban_rg_transfer_certified: int
    proof_gate_pass: int
    promotion_status: str
    interpretation: str


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--out-dir", type=Path, required=True)
    parser.add_argument("--p", type=int, default=7)
    parser.add_argument("--bt-branching-factor", type=int, default=None)
    parser.add_argument(
        "--combo-factor",
        type=int,
        default=None,
        help=(
            "Combinatorial factor in the one-step diameter activity ratio. "
            "Defaults to p+1, matching the current BT p=7 branch count."
        ),
    )
    parser.add_argument("--c-min", type=float, default=0.242)
    parser.add_argument("--entropy-a", type=float, default=0.5)
    parser.add_argument(
        "--row",
        action="append",
        metavar="LABEL:BETA_BARE:BETA_BLOCKED",
        help="Optional row override; may be repeated.",
    )
    parser.add_argument("--all-diameter-certified", action="store_true")
    parser.add_argument("--balaban-rg-transfer-certified", action="store_true")
    return parser.parse_args()


def _safe_exp(x: float) -> float:
    try:
        return math.exp(x)
    except OverflowError:
        return math.inf


def _literal(beta: float, action: float) -> float:
    return abs(_safe_exp(-beta * action) - 1.0)


def _contour(beta: float, c_min: float, entropy_a: float, d: int) -> float:
    return _safe_exp(entropy_a * d - beta * c_min * d)


def _parse_rows(raw_rows: list[str] | None) -> list[tuple[str, float, float]]:
    if not raw_rows:
        return list(DEFAULT_ROWS)
    rows: list[tuple[str, float, float]] = []
    for raw in raw_rows:
        parts = raw.split(":")
        if len(parts) != 3:
            raise ValueError(f"bad --row {raw!r}; expected LABEL:BETA_BARE:BETA_BLOCKED")
        rows.append((parts[0], float(parts[1]), float(parts[2])))
    return rows


def _interpret(row: Sprint54YMScaleRow) -> str:
    if row.proof_gate_pass:
        return "PROOF_GATE_SUPPLIED_NO_CLAY_PROMOTION"
    if row.q_below_one and not row.kp_sum_converges:
        return "Q_BELOW_ONE_BUT_WEIGHTED_KP_SUM_DIVERGES"
    if row.requires_rg_transfer and row.finite_prefix_conditionally_clears:
        return "LITERAL_FAILS_BLOCKED_CONTOUR_PASSES_REQUIRES_BALABAN_TRANSFER"
    if row.kp_passes_blocked_contour:
        return "BLOCKED_CONTOUR_PASSES_BUT_LITERAL_OR_CERTIFICATES_FAIL"
    return "KP_SCALE_ROW_FAILS"


def _compute(args: argparse.Namespace) -> list[Sprint54YMScaleRow]:
    p = int(args.p)
    branching = int(args.bt_branching_factor or (p + 1))
    combo = int(args.combo_factor or branching)
    rows: list[Sprint54YMScaleRow] = []
    for label, beta_bare, beta_blocked in _parse_rows(args.row):
        diameter = 1
        z_literal_bare = _literal(beta_bare, 1.0)
        kp_literal_bare = branching * z_literal_bare
        z_literal_blocked = _literal(beta_blocked, 1.0)
        kp_literal_blocked = branching * z_literal_blocked
        z_unit = _safe_exp(-beta_blocked)
        kp_unit = branching * z_unit
        z_contour = _contour(beta_blocked, args.c_min, args.entropy_a, 1)
        kp_contour = branching * z_contour
        z_contour_d2 = _contour(beta_blocked, args.c_min, args.entropy_a, 2)
        ratio = z_contour_d2 / z_contour if z_contour > 0.0 else math.inf
        activity_ratio_q = combo * ratio
        weighted_kp_sum_ratio = branching * activity_ratio_q
        beta_needed_for_kp_sum = (
            (args.entropy_a + math.log(branching * combo)) / args.c_min
            if args.c_min > 0.0 and branching * combo > 0
            else math.inf
        )
        beta_gap_to_kp_sum = beta_needed_for_kp_sum - beta_blocked
        literal_bare_pass = kp_literal_bare < 1.0
        literal_blocked_pass = kp_literal_blocked < 1.0
        unit_pass = kp_unit < 1.0
        contour_pass = kp_contour < 1.0
        q_below_one = activity_ratio_q < 1.0
        kp_sum_converges = weighted_kp_sum_ratio < 1.0
        requires_rg = (not literal_bare_pass) and contour_pass
        finite_prefix = contour_pass and q_below_one
        proof_gate = (
            finite_prefix
            and kp_sum_converges
            and args.all_diameter_certified
            and args.balaban_rg_transfer_certified
        )
        row = Sprint54YMScaleRow(
            label=label,
            beta_bare=beta_bare,
            beta_blocked=beta_blocked,
            p=p,
            bt_branching_factor=branching,
            c_min=args.c_min,
            entropy_a=args.entropy_a,
            diameter=diameter,
            z_literal_bare=z_literal_bare,
            kp_literal_bare=kp_literal_bare,
            kp_passes_literal_bare=int(literal_bare_pass),
            z_literal_blocked=z_literal_blocked,
            kp_literal_blocked=kp_literal_blocked,
            kp_passes_literal_blocked=int(literal_blocked_pass),
            z_suppressive_unit_blocked=z_unit,
            kp_suppressive_unit_blocked=kp_unit,
            kp_passes_suppressive_unit_blocked=int(unit_pass),
            z_blocked_contour=z_contour,
            kp_blocked_contour=kp_contour,
            kp_passes_blocked_contour=int(contour_pass),
            z_blocked_contour_d2=z_contour_d2,
            geometric_ratio_blocked_d2_d1=ratio,
            combo_factor=combo,
            activity_ratio_q=activity_ratio_q,
            q_below_one=int(q_below_one),
            weighted_kp_sum_ratio=weighted_kp_sum_ratio,
            kp_sum_converges=int(kp_sum_converges),
            beta_needed_for_kp_sum=beta_needed_for_kp_sum,
            beta_gap_to_kp_sum=beta_gap_to_kp_sum,
            requires_rg_transfer=int(requires_rg),
            finite_prefix_conditionally_clears=int(finite_prefix),
            all_diameter_certified=int(args.all_diameter_certified),
            balaban_rg_transfer_certified=int(args.balaban_rg_transfer_certified),
            proof_gate_pass=int(proof_gate),
            promotion_status=PROMOTION_STATUS,
            interpretation="",
        )
        rows.append(Sprint54YMScaleRow(**{**asdict(row), "interpretation": _interpret(row)}))
    return rows


def _jsonable(value: Any) -> Any:
    if isinstance(value, float) and not math.isfinite(value):
        return "inf" if value > 0 else "-inf"
    return value


def _write_csv(path: Path, rows: list[Sprint54YMScaleRow]) -> None:
    with path.open("w", newline="", encoding="utf-8") as handle:
        writer = csv.DictWriter(
            handle,
            fieldnames=list(Sprint54YMScaleRow.__dataclass_fields__.keys()),
        )
        writer.writeheader()
        for row in rows:
            writer.writerow(asdict(row))


def main() -> int:
    args = parse_args()
    args.out_dir.mkdir(parents=True, exist_ok=True)
    rows = _compute(args)
    table_path = args.out_dir / "ym_sprint54_blocked_kp_transfer_table.csv"
    checks_path = args.out_dir / "ym_sprint54_blocked_kp_transfer_checks.json"
    manifest_path = args.out_dir / "ym_sprint54_blocked_kp_transfer_manifest.json"
    _write_csv(table_path, rows)
    carrier = next((row for row in rows if row.label == "rg_flowed_carrier"), rows[-1])
    checks = {
        "pass": bool(any(row.proof_gate_pass for row in rows)),
        "literal_bare_rows_passing": int(sum(row.kp_passes_literal_bare for row in rows)),
        "literal_blocked_rows_passing": int(sum(row.kp_passes_literal_blocked for row in rows)),
        "blocked_contour_rows_passing": int(sum(row.kp_passes_blocked_contour for row in rows)),
        "requires_rg_transfer_rows": int(sum(row.requires_rg_transfer for row in rows)),
        "carrier_label": carrier.label,
        "carrier_kp_literal_blocked": _jsonable(carrier.kp_literal_blocked),
        "carrier_kp_suppressive_unit_blocked": _jsonable(
            carrier.kp_suppressive_unit_blocked
        ),
        "carrier_kp_blocked_contour": _jsonable(carrier.kp_blocked_contour),
        "carrier_geometric_ratio_blocked_d2_d1": _jsonable(
            carrier.geometric_ratio_blocked_d2_d1
        ),
        "carrier_combo_factor": carrier.combo_factor,
        "carrier_activity_ratio_q": _jsonable(carrier.activity_ratio_q),
        "carrier_q_below_one": bool(carrier.q_below_one),
        "carrier_weighted_kp_sum_ratio": _jsonable(carrier.weighted_kp_sum_ratio),
        "carrier_kp_sum_converges": bool(carrier.kp_sum_converges),
        "carrier_beta_needed_for_kp_sum": _jsonable(carrier.beta_needed_for_kp_sum),
        "carrier_beta_gap_to_kp_sum": _jsonable(carrier.beta_gap_to_kp_sum),
        "all_diameter_certified": bool(args.all_diameter_certified),
        "balaban_rg_transfer_certified": bool(args.balaban_rg_transfer_certified),
        "proof_gate_pass": bool(any(row.proof_gate_pass for row in rows)),
        "clay_yang_mills_promoted": False,
        "promotion_status": PROMOTION_STATUS,
        "boundary": (
            "Sprint 54 makes bare-vs-blocked YM KP activity explicit. It does "
            "not prove all-diameter KP or Balaban RG scale transfer. Sprint 55 "
            "uses the same table to record that q<1 is distinct from weighted "
            "KP sum convergence."
        ),
    }
    manifest = {
        "script": Path(__file__).name,
        "receipt_alignment": (
            "DASHI.Physics.Closure."
            "ClaySprintFiftyFourYMInductiveDiameterKPReceipt"
        ),
        "outputs": {
            "table": str(table_path),
            "checks": str(checks_path),
            "manifest": str(manifest_path),
        },
        "promotion_status": PROMOTION_STATUS,
    }
    checks_path.write_text(json.dumps(checks, indent=2, default=_jsonable), encoding="utf-8")
    manifest_path.write_text(json.dumps(manifest, indent=2), encoding="utf-8")
    print(
        f"wrote {table_path}, {checks_path}, {manifest_path}; "
        f"blocked_contour_rows={checks['blocked_contour_rows_passing']} "
        f"proof_gate={checks['proof_gate_pass']} promotion={PROMOTION_STATUS}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
