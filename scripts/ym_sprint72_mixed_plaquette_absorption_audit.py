#!/usr/bin/env python3
"""Sprint 72 YM mixed-plaquette absorption audit.

Sprint 70 showed that treating temporal mixed plaquettes as raw leakage
re-blocks the anisotropic eta=4 KP gate.  Sprint 72 audits the corrected fork:
mixed plaquettes are transfer-matrix/face terms unless a residual fraction
cannot be absorbed without new entropy cost.
"""

from __future__ import annotations

import argparse
import csv
import json
import math
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import Any

from ym_sprint70_boundary_correction_plaquette_audit import (
    ETA_SPATIAL,
    Q_CURRENT,
    enumerate_plaquettes,
    mixed_suppression,
)


DEFAULT_SAFE_RESIDUAL_FRACTION = 0.10
PROMOTION_STATUS = "NO_PROMOTION_SPRINT72_MIXED_PLAQUETTE_ABSORPTION_DIAGNOSTIC"


@dataclass(frozen=True)
class AbsorptionRow:
    plaquette_id: str
    L: int
    dimension: int
    face_type: str
    category: str
    mixed_correction_action: float
    absorbed_face_action: float
    residual_leakage_action: float
    residual_fraction_of_mixed: float
    absorbed_without_entropy_cost: bool
    touches_both_temporal_faces: bool


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--out-dir", type=Path, required=True)
    parser.add_argument("--L", type=int, default=2)
    parser.add_argument("--dimension", type=int, default=4)
    parser.add_argument("--time-axis", type=int, default=0)
    parser.add_argument("--beta", type=float, default=16.7)
    parser.add_argument("--gauge-group-rank", type=int, default=3)
    parser.add_argument(
        "--absorption-policy",
        choices=("face", "manual", "none"),
        default="face",
        help="face absorbs all mixed plaquettes; none treats all as leakage.",
    )
    parser.add_argument(
        "--manual-residual-fraction",
        type=float,
        default=None,
        help="Residual mixed-plaquette fraction for --absorption-policy manual.",
    )
    parser.add_argument(
        "--max-residual-fraction",
        type=float,
        default=DEFAULT_SAFE_RESIDUAL_FRACTION,
    )
    parser.add_argument("--q-current", type=float, default=Q_CURRENT)
    parser.add_argument("--q", type=float, default=None, help="Alias for --q-current.")
    parser.add_argument("--eta-spatial", type=float, default=ETA_SPATIAL)
    return parser.parse_args()


def sprint70_args(args: argparse.Namespace) -> argparse.Namespace:
    return argparse.Namespace(
        L=args.L,
        dimension=args.dimension,
        time_axis=args.time_axis,
        beta=args.beta,
        gauge_group_rank=args.gauge_group_rank,
        suppression_mode="suN-g2",
        decomposition_mode="legacy-correction",
        mixed_coupling_suppression=None,
        face_action_weight=1.0,
        interior_action_weight=1.0,
        boundary_threshold=0.025,
        q_current=args.q_current,
        eta_spatial=args.eta_spatial,
    )


def residual_fraction(args: argparse.Namespace) -> float:
    if args.absorption_policy == "face":
        return 0.0
    if args.absorption_policy == "none":
        return 1.0
    if args.manual_residual_fraction is None:
        raise ValueError("--absorption-policy manual requires --manual-residual-fraction")
    if not 0.0 <= args.manual_residual_fraction <= 1.0:
        raise ValueError("--manual-residual-fraction must be between 0 and 1")
    return args.manual_residual_fraction


def write_csv(path: Path, rows: list[Any]) -> None:
    if not rows:
        path.write_text("", encoding="utf-8")
        return
    with path.open("w", newline="", encoding="utf-8") as handle:
        writer = csv.DictWriter(handle, fieldnames=list(asdict(rows[0]).keys()))
        writer.writeheader()
        for row in rows:
            writer.writerow(asdict(row))


def route_decision(
    touches_both_count: int,
    policy: str,
    residual: float,
    max_residual: float,
    effective_kp_ratio: float,
) -> str:
    if touches_both_count > 0:
        return "TEMPORAL_SPANNING_COUNTEREXAMPLE"
    if policy == "face" and residual == 0.0 and effective_kp_ratio < 1.0:
        return "MIXED_PLAQUETTE_ABSORPTION_CONFIRMED"
    if residual <= max_residual and effective_kp_ratio < 1.0:
        return "RESIDUAL_LEAKAGE_BELOW_10_PERCENT_CONFIRMED"
    if effective_kp_ratio >= 1.0:
        return "MIXED_PLAQUETTES_TRUE_LEAKAGE_REBLOCKS_KP"
    return "RESIDUAL_LEAKAGE_EXCEEDS_SAFE_BOUND"


def main() -> int:
    args = parse_args()
    if args.q is not None:
        args.q_current = args.q
    args.out_dir.mkdir(parents=True, exist_ok=True)

    base_args = sprint70_args(args)
    rows70 = enumerate_plaquettes(base_args)
    residual = residual_fraction(args)
    suppression = mixed_suppression(base_args)

    rows: list[AbsorptionRow] = []
    mixed_action_total = 0.0
    absorbed_face_action_total = 0.0
    residual_leakage_action_total = 0.0
    for row in rows70:
        mixed_action = row.mixed_correction_action
        absorbed = mixed_action * (1.0 - residual)
        leakage = mixed_action * residual
        if mixed_action > 0.0:
            mixed_action_total += mixed_action
            absorbed_face_action_total += absorbed
            residual_leakage_action_total += leakage
        rows.append(
            AbsorptionRow(
                plaquette_id=row.plaquette_id,
                L=row.L,
                dimension=row.dimension,
                face_type=row.face_type,
                category=row.category,
                mixed_correction_action=mixed_action,
                absorbed_face_action=absorbed,
                residual_leakage_action=leakage,
                residual_fraction_of_mixed=residual if mixed_action > 0.0 else 0.0,
                absorbed_without_entropy_cost=(mixed_action > 0.0 and residual == 0.0),
                touches_both_temporal_faces=row.touches_both_temporal_faces,
            )
        )

    touches_both_count = sum(row.touches_both_temporal_faces for row in rows70)
    eta_q = args.eta_spatial * args.q_current
    default_face_correction = suppression
    max_residual_fraction_for_default_c = (
        (math.sqrt(1.0 / eta_q) - 1.0) / default_face_correction
        if eta_q > 0.0 and default_face_correction > 0.0
        else float("inf")
    )
    effective_top_leakage = residual * default_face_correction
    effective_bottom_leakage = residual * default_face_correction
    effective_spatial_leakage = 0.0
    effective_total_leakage_factor = (
        (1.0 + effective_top_leakage)
        * (1.0 + effective_bottom_leakage)
        * (1.0 + effective_spatial_leakage)
    )
    effective_total_leakage_times_4q = effective_total_leakage_factor * eta_q
    route = route_decision(
        touches_both_count,
        args.absorption_policy,
        residual,
        args.max_residual_fraction,
        effective_total_leakage_times_4q,
    )

    summary = {
        "contract": "ym_sprint72_mixed_plaquette_absorption_audit",
        "promotion_status": PROMOTION_STATUS,
        "L": args.L,
        "dimension": args.dimension,
        "time_axis": args.time_axis,
        "beta": args.beta,
        "gauge_group_rank": args.gauge_group_rank,
        "q_current": args.q_current,
        "eta_spatial": args.eta_spatial,
        "four_q": eta_q,
        "default_mixed_correction_per_face": default_face_correction,
        "absorption_policy": args.absorption_policy,
        "residual_fraction": residual,
        "residual_fraction_of_mixed": residual,
        "mixed_plaquettes_face_absorbed": args.absorption_policy == "face",
        "safe_residual_fraction": args.max_residual_fraction,
        "max_residual_fraction_for_default_c": max_residual_fraction_for_default_c,
        "absorption_fraction_of_mixed": 1.0 - residual,
        "mixed_action_total": mixed_action_total,
        "absorbed_face_action_total": absorbed_face_action_total,
        "residual_leakage_action_total": residual_leakage_action_total,
        "residual_top_fraction": residual,
        "residual_bottom_fraction": residual,
        "effective_top_leakage": effective_top_leakage,
        "effective_bottom_leakage": effective_bottom_leakage,
        "effective_spatial_leakage": effective_spatial_leakage,
        "effective_total_leakage_factor": effective_total_leakage_factor,
        "effective_total_leakage_times_4q": effective_total_leakage_times_4q,
        "residual_leakage_bound_passes": residual <= args.max_residual_fraction,
        "kp_bound_passes": effective_total_leakage_times_4q < 1.0,
        "touches_both_temporal_faces_count": touches_both_count,
        "temporal_spanning_counterexample": touches_both_count > 0,
        "mixed_plaquette_absorption_without_entropy_cost_proved": False,
        "residual_leakage_bound_proved": False,
        "temporal_measure_factorization_with_leakage_proved": False,
        "all_diameter_weighted_kp_proved": False,
        "lattice_mass_gap_proved": False,
        "continuum_mass_gap_proved": False,
        "route_decision": route,
        "clay_yang_mills_promoted": False,
    }
    manifest = {
        "diagnostic_mode": "sprint72_mixed_plaquette_absorption_audit",
        "outputs": {
            "absorption_table_csv": "ym_sprint72_mixed_plaquette_absorption_table.csv",
            "summary_json": "ym_sprint72_mixed_plaquette_absorption_summary.json",
        },
        "route_decision": route,
        "promotion_status": PROMOTION_STATUS,
        "clay_yang_mills_promoted": False,
    }

    write_csv(args.out_dir / "ym_sprint72_mixed_plaquette_absorption_table.csv", rows)
    (args.out_dir / "ym_sprint72_mixed_plaquette_absorption_summary.json").write_text(
        json.dumps(summary, indent=2, sort_keys=True),
        encoding="utf-8",
    )
    (args.out_dir / "ym_sprint72_mixed_plaquette_absorption_manifest.json").write_text(
        json.dumps(manifest, indent=2, sort_keys=True),
        encoding="utf-8",
    )
    print(json.dumps(summary, indent=2, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
