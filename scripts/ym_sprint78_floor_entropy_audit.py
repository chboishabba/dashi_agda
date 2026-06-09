#!/usr/bin/env python3
"""Sprint 78 YM floor and entropy-convention audit."""

from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any


SOURCE_FLOOR = 3.079
P0_AT_K8 = 3.057
P0_AT_K9 = 3.124
K_START_SPACETIME = 9
K_START_NC_CONDITIONAL = 0
Q_CURRENT = 0.23178189475262734
ETA_GENERIC_4D = 8
ETA_FINE_LATTICE_SPATIAL = 6
ETA_SPATIAL_TRANSFER = 4
BLOCKING_FACTOR = 2
SPATIAL_DIMENSION = 3
MAX_SPATIAL_BLOCK_FACES = 2 * SPATIAL_DIMENSION
TEMPORAL_FACES_ABSORBED_INTO_TK = 2
RESIDUAL_FACES = MAX_SPATIAL_BLOCK_FACES - TEMPORAL_FACES_ABSORBED_INTO_TK


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--out-dir", type=Path, required=True)
    return parser.parse_args()


def payload() -> dict[str, Any]:
    fine_lattice_ratio = ETA_FINE_LATTICE_SPATIAL * Q_CURRENT
    spatial_ratio = ETA_SPATIAL_TRANSFER * Q_CURRENT
    generic_ratio = ETA_GENERIC_4D * Q_CURRENT
    eta6_threshold = 1.0 / ETA_FINE_LATTICE_SPATIAL
    eta6_reduction_needed = (Q_CURRENT - eta6_threshold) / Q_CURRENT
    return {
        "contract": "ym_sprint78_floor_entropy_audit",
        "source_floor": SOURCE_FLOOR,
        "p0_at_k8": P0_AT_K8,
        "p0_at_k9": P0_AT_K9,
        "p0_k8_below_source_floor": P0_AT_K8 < SOURCE_FLOOR,
        "p0_k9_above_source_floor": P0_AT_K9 > SOURCE_FLOOR,
        "k_start_spacetime_floor": K_START_SPACETIME,
        "k_start_spacetime_floor_is_not_one": K_START_SPACETIME != 1,
        "k_start_spacetime_floor_is_not_fifty": K_START_SPACETIME != 50,
        "k_start_nc_floor_conditional": K_START_NC_CONDITIONAL,
        "nc_absorption_floor_authority_cited": True,
        "nc_absorption_floor_authority_assumed": True,
        "nc_absorption_floor_authority_proved": False,
        "nc_absorption_floor_authority_formal_derivation_in_repo": False,
        "k_start_under_nc_absorption_floor_authority": 0,
        "nc_absorption_floor_authority_gives_k_start_zero": True,
        "finite_prefix_gap": "k=0..8",
        "blocking_factor": BLOCKING_FACTOR,
        "spatial_dimension": SPATIAL_DIMENSION,
        "max_spatial_block_faces": MAX_SPATIAL_BLOCK_FACES,
        "temporal_faces_absorbed_into_Tk": TEMPORAL_FACES_ABSORBED_INTO_TK,
        "residual_faces": RESIDUAL_FACES,
        "entropy_convention": "L2_BLOCKING_ORIENTATIONS",
        "hypercubic_nearest_neighbour_3d_count": 6,
        "hypercubic_nearest_neighbour_3d_accepted_for_eta4": False,
        "seiler_2d_minus_2_3d_count": 4,
        "seiler_2d_minus_2_matches_repo_generic_4d_eta8": False,
        "eta_generic_4d": ETA_GENERIC_4D,
        "fine_lattice_spatial_eta": ETA_FINE_LATTICE_SPATIAL,
        "eta_spatial_transfer": ETA_SPATIAL_TRANSFER,
        "blocked_l2_spatial_eta": ETA_SPATIAL_TRANSFER,
        "q_current": Q_CURRENT,
        "fine_lattice_spatial_eta_q": fine_lattice_ratio,
        "fine_lattice_spatial_kp_arithmetic_closes": fine_lattice_ratio < 1.0,
        "fine_lattice_eta6_formally_excluded": True,
        "eta6_q_threshold": eta6_threshold,
        "q_reduction_needed_for_eta6_fraction": eta6_reduction_needed,
        "q_reduction_needed_for_eta6_percent": 100.0 * eta6_reduction_needed,
        "spatial_transfer_eta_q": spatial_ratio,
        "blocked_l2_spatial_eta_q": spatial_ratio,
        "generic_4d_eta_q": generic_ratio,
        "anisotropic_kp_arithmetic_closes": spatial_ratio < 1.0,
        "blocked_l2_kp_arithmetic_closes": spatial_ratio < 1.0,
        "generic_4d_kp_arithmetic_fails": generic_ratio > 1.0,
        "effective_action_polymers_spatial_only_proved": False,
        "kp_entropy_from_l2_blocking_orientations_proved": False,
        "kp_entropy_at_blocked_scale_l2_proved": False,
        "polymer_defined_on_blocked_lattice_proved": False,
        "temporal_entropy_quotient_halves_generic_4d_count_proved": False,
        "clay_yang_mills_promoted": False,
    }


def main() -> int:
    args = parse_args()
    args.out_dir.mkdir(parents=True, exist_ok=True)
    data = payload()
    (args.out_dir / "ym_sprint78_floor_entropy_summary.json").write_text(
        json.dumps(data, indent=2, sort_keys=True) + "\n",
        encoding="utf-8",
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
