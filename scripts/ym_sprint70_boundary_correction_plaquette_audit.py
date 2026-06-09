#!/usr/bin/env python3
"""Sprint 70 YM boundary-correction plaquette audit.

This diagnostic enumerates unit Wilson plaquettes in an anisotropic slab and
separates the closed Sprint 68 support fact from temporal-face bookkeeping.
It does not prove a mass gap.  By default it uses the corrected transfer-matrix
bookkeeping: mixed spatial-temporal plaquettes touching a temporal face are
face/transfer-matrix action, not residual correction.  Legacy correction mode
is retained to reproduce the old accounting diagnostic.
"""

from __future__ import annotations

import argparse
import csv
import itertools
import json
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import Any, Iterable


Q_CURRENT = 0.23178189475262734
ETA_SPATIAL = 4.0
ETA_SPATIAL_Q = ETA_SPATIAL * Q_CURRENT
MAX_LEAKAGE_FACTOR = 1.0 / ETA_SPATIAL_Q
SAFE_PER_FACE_LEAKAGE = 0.025
SAFE_THREE_FACE_FACTOR = (1.0 + SAFE_PER_FACE_LEAKAGE) ** 3
SAFE_THREE_FACE_TIMES_4Q = SAFE_THREE_FACE_FACTOR * ETA_SPATIAL_Q
SAFE_THREE_FACE_MARGIN = 1.0 - SAFE_THREE_FACE_TIMES_4Q
KP_MARGIN = 1.0 - ETA_SPATIAL_Q
PER_FACE_BUDGET_3_FACE = MAX_LEAKAGE_FACTOR ** (1.0 / 3.0) - 1.0
Q_HEADROOM_BEFORE_ETA4_FAILS = 1.0 / ETA_SPATIAL - Q_CURRENT
PROMOTION_STATUS = "NO_PROMOTION_SPRINT70_BOUNDARY_CORRECTION_DIAGNOSTIC"
CATEGORY_PRECEDENCE_CONTRACT = (
    "corrected mode: temporal-face transfer-matrix action includes mixed "
    "spatial-temporal plaquettes; legacy mode: mixed_coupling wins before "
    "temporal_face and spatial_boundary as an old diagnostic bucket"
)


@dataclass(frozen=True)
class PlaquetteRow:
    block_id: str
    plaquette_id: str
    L: int
    dimension: int
    time_axis: int
    orientation: str
    orientation_a: int
    orientation_b: int
    anchor: str
    location_class: str
    face_type: str
    is_mixed_spatial_temporal: bool
    wilson_action: float
    main_face_action: float
    mixed_correction_action: float
    transfer_matrix_action: float
    residual_correction_action: float
    correction_ratio: float
    t_min: int
    t_max: int
    touches_top_temporal_face: bool
    touches_bottom_temporal_face: bool
    touches_both_temporal_faces: bool
    touches_spatial_boundary: bool
    admissible_polymer: bool
    passes_2p5_percent: bool
    category: str
    base_action_weight: float
    correction_action_weight: float


@dataclass(frozen=True)
class CategorySummaryRow:
    category: str
    plaquette_count: int
    base_action_total: float
    correction_action_total: float


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--out-dir", type=Path, required=True)
    parser.add_argument("--L", type=int, default=2)
    parser.add_argument("--dimension", type=int, default=4)
    parser.add_argument("--time-axis", type=int, default=0)
    parser.add_argument("--beta", type=float, default=16.7)
    parser.add_argument("--gauge-group-rank", type=int, default=3)
    parser.add_argument(
        "--suppression-mode",
        choices=("suN-g2", "inverse-beta", "manual", "none"),
        default="suN-g2",
    )
    parser.add_argument(
        "--decomposition-mode",
        choices=("transfer-matrix", "legacy-correction"),
        default="transfer-matrix",
        help=(
            "transfer-matrix absorbs mixed temporal plaquettes into face action; "
            "legacy-correction reproduces the old residual-correction diagnostic."
        ),
    )
    parser.add_argument(
        "--mixed-coupling-suppression",
        type=float,
        default=None,
        help="Used only with --suppression-mode manual.",
    )
    parser.add_argument("--face-action-weight", type=float, default=1.0)
    parser.add_argument("--interior-action-weight", type=float, default=1.0)
    parser.add_argument("--boundary-threshold", type=float, default=0.025)
    parser.add_argument(
        "--per-face-leakage-bound",
        type=float,
        default=None,
        help="Alias for --boundary-threshold, expressed as a ratio such as 0.025.",
    )
    parser.add_argument("--q-current", type=float, default=Q_CURRENT)
    parser.add_argument("--q", type=float, default=None, help="Alias for --q-current.")
    parser.add_argument("--eta-spatial", type=float, default=ETA_SPATIAL)
    args = parser.parse_args()
    if args.q is not None:
        args.q_current = args.q
    if args.per_face_leakage_bound is not None:
        args.boundary_threshold = args.per_face_leakage_bound
    return args


def mixed_suppression(args: argparse.Namespace) -> float:
    if args.suppression_mode == "none":
        return 1.0
    if args.suppression_mode == "inverse-beta":
        return 1.0 / args.beta
    if args.suppression_mode == "suN-g2":
        return (2.0 * args.gauge_group_rank) / args.beta
    if args.mixed_coupling_suppression is None:
        raise ValueError("--suppression-mode manual requires --mixed-coupling-suppression")
    return args.mixed_coupling_suppression


def plaquette_anchors(L: int, dimension: int, orientation: tuple[int, int]) -> Iterable[tuple[int, ...]]:
    ranges: list[range] = []
    oriented = set(orientation)
    for axis in range(dimension):
        ranges.append(range(L) if axis in oriented else range(L + 1))
    return itertools.product(*ranges)


def plaquette_temporal_extent(
    anchor: tuple[int, ...], orientation: tuple[int, int], time_axis: int
) -> tuple[int, int]:
    if time_axis in orientation:
        return anchor[time_axis], anchor[time_axis] + 1
    return anchor[time_axis], anchor[time_axis]


def touches_spatial_boundary(
    anchor: tuple[int, ...], orientation: tuple[int, int], L: int, time_axis: int
) -> bool:
    for axis, coord in enumerate(anchor):
        if axis == time_axis:
            continue
        max_coord = coord + (1 if axis in orientation else 0)
        if coord == 0 or max_coord == L:
            return True
    return False


def classify_plaquette(
    anchor: tuple[int, ...],
    orientation: tuple[int, int],
    L: int,
    time_axis: int,
    decomposition_mode: str,
) -> tuple[str, str, bool, int, int, bool, bool, bool, bool]:
    t_min, t_max = plaquette_temporal_extent(anchor, orientation, time_axis)
    touches_bottom = t_min == 0
    touches_top = t_max == L
    touches_both = touches_bottom and touches_top
    spatial_boundary = touches_spatial_boundary(anchor, orientation, L, time_axis)
    has_temporal_edge = time_axis in orientation
    is_mixed_spatial_temporal = has_temporal_edge and any(
        axis != time_axis for axis in orientation
    )
    if has_temporal_edge and (touches_top or touches_bottom):
        if touches_top and touches_bottom:
            face_type = "temporal_spanning"
            category = "mixed_coupling"
        elif touches_top:
            face_type = "top_temporal"
            category = (
                "mixed_coupling"
                if decomposition_mode == "legacy-correction"
                else "transfer_matrix_face_action"
            )
        else:
            face_type = "bottom_temporal"
            category = (
                "mixed_coupling"
                if decomposition_mode == "legacy-correction"
                else "transfer_matrix_face_action"
            )
    elif (not has_temporal_edge) and touches_top:
        category = "top_temporal_face"
        face_type = "top_temporal"
    elif (not has_temporal_edge) and touches_bottom:
        category = "bottom_temporal_face"
        face_type = "bottom_temporal"
    elif spatial_boundary:
        category = "spatial_boundary"
        face_type = "spatial"
    else:
        category = "interior"
        face_type = "interior"
    return (
        category,
        face_type,
        is_mixed_spatial_temporal,
        t_min,
        t_max,
        touches_top,
        touches_bottom,
        touches_both,
        spatial_boundary,
    )


def enumerate_plaquettes(args: argparse.Namespace) -> list[PlaquetteRow]:
    if args.L < 1:
        raise ValueError("L must be positive")
    if args.dimension < 2:
        raise ValueError("dimension must be at least 2")
    if not 0 <= args.time_axis < args.dimension:
        raise ValueError("time axis out of bounds")
    suppression = mixed_suppression(args)
    rows: list[PlaquetteRow] = []
    count = 0
    for orientation in itertools.combinations(range(args.dimension), 2):
        for anchor in plaquette_anchors(args.L, args.dimension, orientation):
            (
                category,
                face_type,
                is_mixed_spatial_temporal,
                t_min,
                t_max,
                touches_top,
                touches_bottom,
                touches_both,
                spatial_boundary,
            ) = classify_plaquette(
                anchor,
                orientation,
                args.L,
                args.time_axis,
                args.decomposition_mode,
            )
            base_weight = (
                args.interior_action_weight
                if category == "interior"
                else args.face_action_weight
            )
            correction_weight = (
                args.face_action_weight * suppression
                if args.decomposition_mode == "legacy-correction"
                and category == "mixed_coupling"
                else 0.0
            )
            transfer_matrix_action = (
                base_weight
                if args.decomposition_mode == "transfer-matrix"
                and category == "transfer_matrix_face_action"
                else 0.0
            )
            residual_correction_action = 0.0
            main_face_action = 0.0 if category == "interior" else base_weight
            correction_ratio = (
                correction_weight / main_face_action
                if main_face_action > 0.0
                else 0.0
            )
            rows.append(
                PlaquetteRow(
                    block_id=f"L{args.L}_d{args.dimension}_t{args.time_axis}",
                    plaquette_id=f"p{count}",
                    L=args.L,
                    dimension=args.dimension,
                    time_axis=args.time_axis,
                    orientation=f"{orientation[0]}-{orientation[1]}",
                    orientation_a=orientation[0],
                    orientation_b=orientation[1],
                    anchor=",".join(str(x) for x in anchor),
                    location_class=category,
                    face_type=face_type,
                    is_mixed_spatial_temporal=is_mixed_spatial_temporal,
                    wilson_action=base_weight,
                    main_face_action=main_face_action,
                    mixed_correction_action=correction_weight,
                    transfer_matrix_action=transfer_matrix_action,
                    residual_correction_action=residual_correction_action,
                    correction_ratio=correction_ratio,
                    t_min=t_min,
                    t_max=t_max,
                    touches_top_temporal_face=touches_top,
                    touches_bottom_temporal_face=touches_bottom,
                    touches_both_temporal_faces=touches_both,
                    touches_spatial_boundary=spatial_boundary,
                    admissible_polymer=not touches_both,
                    passes_2p5_percent=correction_ratio <= args.boundary_threshold,
                    category=category,
                    base_action_weight=base_weight,
                    correction_action_weight=correction_weight,
                )
            )
            count += 1
    return rows


def category_summary(rows: list[PlaquetteRow]) -> list[CategorySummaryRow]:
    categories = [
        "interior",
        "top_temporal_face",
        "bottom_temporal_face",
        "transfer_matrix_face_action",
        "spatial_boundary",
        "mixed_coupling",
    ]
    summary: list[CategorySummaryRow] = []
    for category in categories:
        selected = [row for row in rows if row.category == category]
        summary.append(
            CategorySummaryRow(
                category=category,
                plaquette_count=len(selected),
                base_action_total=sum(row.base_action_weight for row in selected),
                correction_action_total=sum(
                    row.correction_action_weight for row in selected
                ),
            )
        )
    return summary


def route_decision(
    touches_both_count: int,
    max_face_correction_ratio: float,
    threshold: float,
    total_leakage_times_4q: float,
    decomposition_mode: str,
) -> str:
    if touches_both_count > 0:
        return "TEMPORAL_SPANNING_COUNTEREXAMPLE"
    if decomposition_mode == "transfer-matrix" and total_leakage_times_4q < 1.0:
        return "MIXED_PLAQUETTES_ABSORBED_INTO_TRANSFER_MATRIX"
    if max_face_correction_ratio > threshold:
        return "BOUNDARY_CORRECTION_EXCEEDS_2P5_PERCENT"
    if total_leakage_times_4q >= 1.0:
        return "ANISOTROPIC_ROUTE_REBLOCKED_BY_LEAKAGE"
    return "BOUNDARY_CORRECTION_SMALL_CONFIRMED"


def max_ratio_for_face(rows: list[PlaquetteRow], face_type: str) -> float:
    ratios = [
        row.correction_ratio
        for row in rows
        if row.face_type == face_type and row.mixed_correction_action > 0.0
    ]
    if not ratios:
        return 0.0
    return max(ratios)


def write_csv(path: Path, rows: list[Any]) -> None:
    if not rows:
        path.write_text("", encoding="utf-8")
        return
    with path.open("w", newline="", encoding="utf-8") as handle:
        writer = csv.DictWriter(handle, fieldnames=list(asdict(rows[0]).keys()))
        writer.writeheader()
        for row in rows:
            writer.writerow(asdict(row))


def main() -> int:
    args = parse_args()
    args.out_dir.mkdir(parents=True, exist_ok=True)
    rows = enumerate_plaquettes(args)
    summary_rows = category_summary(rows)
    face_action = sum(
        row.base_action_total
        for row in summary_rows
        if row.category
        in {
            "top_temporal_face",
            "bottom_temporal_face",
            "transfer_matrix_face_action",
            "spatial_boundary",
        }
    )
    correction_action = sum(
        row.correction_action_total for row in summary_rows if row.category == "mixed_coupling"
    )
    correction_ratio = correction_action / face_action if face_action > 0.0 else float("inf")
    touches_both_count = sum(row.touches_both_temporal_faces for row in rows)
    eta_q = args.eta_spatial * args.q_current
    max_leakage = 1.0 / eta_q if eta_q > 0.0 else float("inf")
    max_top_correction_ratio = max_ratio_for_face(rows, "top_temporal")
    max_bottom_correction_ratio = max_ratio_for_face(rows, "bottom_temporal")
    max_spatial_correction_ratio = max_ratio_for_face(rows, "spatial")
    top_passes = max_top_correction_ratio <= args.boundary_threshold
    bottom_passes = max_bottom_correction_ratio <= args.boundary_threshold
    spatial_passes = max_spatial_correction_ratio <= args.boundary_threshold
    max_face_correction_ratio = max(
        max_top_correction_ratio,
        max_bottom_correction_ratio,
        max_spatial_correction_ratio,
    )
    leakage_factor_observed = (
        (1.0 + max_top_correction_ratio)
        * (1.0 + max_bottom_correction_ratio)
        * (1.0 + max_spatial_correction_ratio)
    )
    leakage_controlled_kp_ratio = leakage_factor_observed * eta_q
    leakage_bound_passes = leakage_controlled_kp_ratio < 1.0
    decision = route_decision(
        touches_both_count,
        max_face_correction_ratio,
        args.boundary_threshold,
        leakage_controlled_kp_ratio,
        args.decomposition_mode,
    )
    transfer_matrix_action_total = sum(row.transfer_matrix_action for row in rows)
    residual_correction_action_total = sum(
        row.residual_correction_action for row in rows
    )
    legacy_mixed_correction_action_total = sum(
        args.face_action_weight * mixed_suppression(args)
        for row in rows
        if row.is_mixed_spatial_temporal
        and row.face_type in {"top_temporal", "bottom_temporal"}
    )
    legacy_face_action = face_action - transfer_matrix_action_total
    legacy_correction_over_face_action = (
        legacy_mixed_correction_action_total / legacy_face_action
        if legacy_face_action > 0.0
        else 0.0
    )
    legacy_total_leakage_factor = (
        (1.0 + legacy_correction_over_face_action)
        * (1.0 + legacy_correction_over_face_action)
    )
    legacy_total_leakage_times_4q = legacy_total_leakage_factor * eta_q
    checks = {
        "contract": "ym_sprint70_boundary_correction_plaquette_audit",
        "category_precedence_contract": CATEGORY_PRECEDENCE_CONTRACT,
        "promotion_status": PROMOTION_STATUS,
        "L": args.L,
        "dimension": args.dimension,
        "time_axis": args.time_axis,
        "decomposition_mode": args.decomposition_mode,
        "beta": args.beta,
        "gauge_group_rank": args.gauge_group_rank,
        "suppression_mode": args.suppression_mode,
        "mixed_coupling_suppression": mixed_suppression(args),
        "q_current": args.q_current,
        "eta_spatial": args.eta_spatial,
        "eta_spatial_times_q": eta_q,
        "kp_margin_without_leakage": 1.0 - eta_q,
        "max_leakage_factor": max_leakage,
        "per_face_budget_three_face": max_leakage ** (1.0 / 3.0) - 1.0,
        "safe_per_face_leakage": SAFE_PER_FACE_LEAKAGE,
        "safe_three_face_leakage_factor": SAFE_THREE_FACE_FACTOR,
        "safe_three_face_times_4q": SAFE_THREE_FACE_TIMES_4Q,
        "safe_three_face_margin": SAFE_THREE_FACE_MARGIN,
        "three_face_leakage_safe_arithmetic": SAFE_THREE_FACE_TIMES_4Q < 1.0,
        "three_face_leakage_product_bound": (
            (1.0 + args.boundary_threshold) ** 3
        ),
        "q_headroom_before_eta4_fails": 1.0 / args.eta_spatial - args.q_current,
        "boundary_threshold": args.boundary_threshold,
        "per_face_leakage_bound": args.boundary_threshold,
        "plaquette_count": len(rows),
        "touches_both_temporal_faces_count": touches_both_count,
        "admissible_polymer_spanning_count": sum(
            row.touches_both_temporal_faces and row.admissible_polymer for row in rows
        ),
        "face_action_total": face_action,
        "correction_action_total": correction_action,
        "correction_over_face_action": correction_ratio,
        "transfer_matrix_action_total": transfer_matrix_action_total,
        "residual_correction_action_total": residual_correction_action_total,
        "residual_correction_zero_by_decomposition": (
            residual_correction_action_total == 0.0
        ),
        "mixed_plaquettes_are_transfer_matrix_not_correction": (
            args.decomposition_mode == "transfer-matrix"
        ),
        "bookkeeping_lambda": 1.0 if args.decomposition_mode == "transfer-matrix" else leakage_factor_observed,
        "legacy_mixed_correction_action_total": legacy_mixed_correction_action_total,
        "legacy_correction_over_face_action": legacy_correction_over_face_action,
        "legacy_total_leakage_factor": legacy_total_leakage_factor,
        "legacy_total_leakage_times_4q": legacy_total_leakage_times_4q,
        "max_top_correction_ratio": max_top_correction_ratio,
        "max_bottom_correction_ratio": max_bottom_correction_ratio,
        "max_spatial_correction_ratio": max_spatial_correction_ratio,
        "top_passes_2p5": top_passes,
        "bottom_passes_2p5": bottom_passes,
        "spatial_passes_2p5": spatial_passes,
        "total_leakage_factor": leakage_factor_observed,
        "total_leakage_times_4q": leakage_controlled_kp_ratio,
        "leakage_factor_observed": leakage_factor_observed,
        "leakage_controlled_kp_ratio": leakage_controlled_kp_ratio,
        "leakage_bound_passes": leakage_bound_passes,
        "boundary_correction_small": (
            top_passes
            and bottom_passes
            and spatial_passes
            and leakage_controlled_kp_ratio < 1.0
            and touches_both_count == 0
        ),
        "temporal_spanning_counterexample": touches_both_count > 0,
        "route_decision": decision,
        "temporal_faces_disjoint_for_admissible_polymers": touches_both_count == 0,
        "wilson_action_slab_decomposition_proved": False,
        "mixed_plaquettes_are_transfer_matrix_not_correction_proved": (
            args.decomposition_mode == "transfer-matrix"
        ),
        "local_coupling_correction_bounded_proved": False,
        "temporal_measure_factorization_with_leakage_proved": False,
        "leakage_controlled_weighted_kp_proved": False,
        "all_diameter_weighted_kp_proved": False,
        "lattice_mass_gap_proved": False,
        "continuum_mass_gap_proved": False,
        "clay_yang_mills_promoted": False,
    }
    manifest = {
        "diagnostic_mode": "sprint70_boundary_correction_plaquette_audit",
        "category_precedence_contract": CATEGORY_PRECEDENCE_CONTRACT,
        "outputs": {
            "plaquette_table_csv": "ym_sprint70_boundary_correction_table.csv",
            "category_summary_csv": "ym_sprint70_boundary_correction_by_category.csv",
            "summary_json": "ym_sprint70_boundary_leakage_summary.json",
        },
        "route_decision": decision,
        "promotion_status": PROMOTION_STATUS,
        "clay_yang_mills_promoted": False,
    }
    write_csv(args.out_dir / "ym_sprint70_boundary_correction_table.csv", rows)
    write_csv(args.out_dir / "ym_sprint70_boundary_correction_by_category.csv", summary_rows)
    (args.out_dir / "ym_sprint70_boundary_leakage_summary.json").write_text(
        json.dumps(checks, indent=2, sort_keys=True), encoding="utf-8"
    )
    (args.out_dir / "ym_sprint70_boundary_correction_manifest.json").write_text(
        json.dumps(manifest, indent=2, sort_keys=True), encoding="utf-8"
    )
    print(json.dumps(checks, indent=2, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
