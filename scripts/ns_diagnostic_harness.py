#!/usr/bin/env python3
"""NS diagnostic harness for the DASHI residue bridge.

This is an evidence-only bridge falsifier.  It consumes a truth NPZ with
``omega_snapshots`` and ``steps`` and writes:

* ``ns_diagnostic_table.csv`` with one row per shell/time sample
* ``ns_residue_semantics_audit.csv`` with side-by-side R+ definitions
* ``ns_residue_semantics_wide.csv`` with one row per shell/time/theta
* ``ns_budget_component_audit.csv`` with Sprint 45 gamma/eta/beta budget terms
* ``ns_packet_transition_table.csv`` with Sprint 47 coarse packet lineage rows
* ``ns_replenishment_decomposition.csv`` with Sprint 48 source component rows
* ``ns_material_parent_summary.csv``/``.json`` with Sprint 49 material-parent replay rows
* ``ns_ternary_cross_shell_summary.json`` with Sprint 50 ternary cross-shell replay evidence
* ``ns_diagnostic_checks.json`` with pass/fail summaries
* ``ns_diagnostic_manifest.json`` with input and governance metadata

The trusted sibling ``../dashiCFD`` truth artifacts are currently 2D scalar
vorticity traces.  For those traces the 3D vortex-stretching bridge is not
available; the harness records a fail-closed 2D-embedded diagnostic where
physical stretching is identically zero.  If supplied with 3D vector vorticity
snapshots shaped ``(T,N,N,N,3)``, it computes the spectral shell quantities
directly on the periodic box.

For Sprint 48 replenishment-only work, ``--replay-packet-summary`` consumes an
existing Sprint 47 ``ns_packet_transition_summary.csv`` and writes the Sprint
48 decomposition artifacts without loading truth snapshots or recomputing FFTs.
For Sprint 49 material-parent work, ``--replay-material-parent-summary``
consumes the GPU-produced dashiCFD material parent summary and writes
lightweight replay receipts without recomputing N64 shell/packet diagnostics.
For Sprint 50 ternary cross-shell work, ``--replay-ternary-cross-shell-summary``
consumes the dashiCFD summary JSON and optional sibling matrix/decomposition
CSVs without recomputing material-parent lineage.
"""

from __future__ import annotations

import argparse
import csv
import json
import math
import os
import shutil
import sys
import time as time_module
from dataclasses import dataclass
from pathlib import Path
from typing import Any, Iterable

import numpy as np


EPS = 1e-30


@dataclass(frozen=True)
class HarnessRow:
    K: int
    t: float
    omega_l2_sq: float
    D_K: float
    T_K: float
    Q_K: float
    Rminus_K: float
    Rzero_K: float
    Rplus_K: float
    netResidue_K: float
    BeltramiDefect_K: float
    DirectionCoherenceDefect_K: float
    PressureDecorrelationScore_K: float
    AlignedConcentration_K: float
    M_plus_minus: float
    M_plus_zero: float
    M_plus_plus: float
    s_K: float
    s_eff_K: float
    weighted_s_eff_K: float
    C_K: float
    gamma_K: float
    eta_K: float
    p: int
    beta_K: float
    theta: float
    budget_K: float
    rho_K: float
    passBudget: int
    diagnostic_mode: str


@dataclass(frozen=True)
class BridgeBudgetRow:
    step: int
    time: float
    K: int
    shell_enstrophy: float
    tail_enstrophy: float
    D_K: float
    theta_NS_K: str
    Q_K_proxy: str
    R_plus_K_proxy: str
    aligned_concentration_K: str
    beta_hat_K: str
    gamma_hat_K: str
    eta_hat_K: str
    budget_hat_K: str
    adjusted_bridge_ratio: str
    promotion_status: str
    field_status: str
    unavailable_reason: str
    diagnostic_mode: str


@dataclass(frozen=True)
class ResidueAuditRow:
    step: int
    time: float
    K: int
    theta: float
    semantic: str
    semantic_status: str
    Q_K: str
    aligned_concentration_K: str
    R_plus_K: str
    adjusted_bridge_ratio: str
    beta_hat_K: str
    gamma_hat_K: str
    eta_hat_K: str
    budget_hat_K: str
    zeroR_positiveQ: int
    ratio_available: int
    budget_pass: int
    promotion_status: str
    note: str


@dataclass(frozen=True)
class ResidueThetaSummaryRow:
    theta: float
    semantic: str
    semantic_status: str
    rows: int
    ratio_available_rows: int
    zeroR_positiveQ_rows: int
    budget_pass_rows: int
    sup_adjusted_bridge_ratio: str
    median_adjusted_bridge_ratio: str
    p95_adjusted_bridge_ratio: str
    inf_budget_hat_K: str
    all_budget_pass: int
    all_ratios_available: int
    interpretation: str
    promotion_status: str


@dataclass(frozen=True)
class ResidueWideRow:
    step: int
    time: float
    K: int
    theta: float
    Q_K: str
    Conc_K: str
    Rplus_strict: str
    Rplus_strain: str
    Rplus_stretchSign: str
    Rplus_pressureRelaxed: str
    Rplus_noPressure: str
    C_strict: str
    C_strain: str
    C_stretchSign: str
    C_pressureRelaxed: str
    C_noPressure: str
    zeroR_positiveQ_strict: int
    zeroR_positiveQ_strain: int
    zeroR_positiveQ_stretchSign: int
    zeroR_positiveQ_pressureRelaxed: int
    zeroR_positiveQ_noPressure: int


@dataclass(frozen=True)
class BudgetComponentAuditRow:
    step: int
    time: float
    K: int
    theta: float
    residue_key: str
    p: int
    Q_K: str
    source_K: str
    aligned_concentration_K: str
    beta_fit: str
    gamma_fit: str
    eta_fit: str
    eta_log2p_fit: str
    budget_without_concentration_gamma_only: str
    budget_with_concentration_gamma_only: str
    budget_if_gamma_only: str
    budget_if_eta_only: str
    budget_if_independent_gamma_eta: str
    budget_gap_gamma_only: str
    budget_gap_eta_only: str
    budget_gap_independent_gamma_eta: str
    same_observable_gamma_eta: int
    independent_gamma_eta: int
    double_count_warning: str
    budget_status: str
    promotion_status: str
    note: str


@dataclass(frozen=True)
class SourceDecaySearchRow:
    step: int
    time: float
    K: int
    theta: float
    residue_key: str
    Rplus: str
    rho_K: str
    rho_pass: int
    angular_coherence: str
    angular_sigma_fit: str
    angular_candidate_budget: str
    pressure_survival: str
    pressure_sigma_fit: str
    pressure_candidate_budget: str
    beta_fit: str
    candidate_budget: str
    bt_eta_status: str
    independent_of_Rplus: int
    independent_of_Q: int
    used_in_budget: int
    double_count_warning: str
    route_status: str
    promotion_status: str
    note: str


@dataclass(frozen=True)
class PacketTransitionRow:
    step: int
    time: float
    K: int
    packet_id: str
    parent_packet_id: str
    state_K: str
    state_Kplus1: str
    mass_K: str
    mass_Kplus1: str
    overlap_score: str
    centroid_distance: str
    direction_angle: str
    BT_lane_id: str
    braid_word_id_proxy: str
    transition_status: str
    note: str


@dataclass(frozen=True)
class PacketTransitionSummaryRow:
    step: int
    time: float
    K: int
    packet_count_K: int
    packet_count_Kplus1: int
    Rplus_K: str
    Rzero_K: str
    Rminus_K: str
    M_plus_plus: str
    M_plus_zero: str
    M_plus_minus: str
    s_eff_K: str
    weighted_s_eff_K: str
    rho_packet_K: str
    pass_persistence: int
    pass_source_prefix: int
    route_status: str
    promotion_status: str
    note: str


@dataclass(frozen=True)
class ReplenishmentDecompositionRow:
    step: int
    time: float
    K: int
    Rminus_K: str
    Rzero_K: str
    Rplus_K: str
    M_plus_plus: str
    M_plus_zero: str
    M_plus_minus: str
    source_from_plus: str
    source_from_zero: str
    source_from_minus: str
    source_new_unmatched: str
    source_total_eff: str
    weighted_plus_source: str
    weighted_zero_source: str
    weighted_minus_source: str
    weighted_new_source: str
    weighted_total_source: str
    sigma_zero_fit: str
    sigma_minus_fit: str
    sigma_new_fit: str
    sigma_total_fit: str
    pass_persistence: int
    pass_zero_source: int
    pass_minus_source: int
    pass_new_source: int
    pass_total_source: int
    route_status: str
    promotion_status: str
    note: str


@dataclass(frozen=True)
class MaterialParentSummaryRow:
    time: float
    K_child: int
    M_plus_plus_material: str
    source_true_new: str
    source_tracking_uncertain: str
    source_cross_shell: str
    source_low_shell_injection: str
    source_total_material: str
    weighted_true_new: str
    weighted_tracking_uncertain: str
    weighted_cross_shell: str
    weighted_low_shell_injection: str
    weighted_total_material: str
    sigma_true_new_fit: str
    sigma_tracking_uncertain_fit: str
    sigma_cross_shell_fit: str
    sigma_low_shell_fit: str
    sigma_total_material_fit: str
    route_status: str


TERNARY_CROSS_SHELL_REQUIRED_SUMMARY_FIELDS = {
    "contract",
    "diagnostic_mode",
    "weighted_cross_plus_from_minus",
    "weighted_cross_plus_from_zero",
    "weighted_cross_plus_from_plus",
    "sigma_cross_from_minus",
    "sigma_cross_from_zero",
    "sigma_cross_from_plus",
    "dominant_red_source_state",
    "dominant_red_source_kind",
    "route_decision",
    "BT_distance_proxy",
    "classification_field_used_for_source_kind",
    "full_ternary_matrix_available",
    "adjacent_only_theorem_sufficient",
    "cross_shell_summability_proved",
    "bt_distance_decay_theorem_proved",
    "clay_promotion",
    "navier_stokes_promotion",
}

SIGNED_TERNARY_FLIP_REQUIRED_SUMMARY_FIELDS = {
    "contract",
    "diagnostic_mode",
    "ternary_involution_semantics",
    "weighted_cross_minus_to_plus",
    "weighted_cross_plus_to_minus",
    "signed_flip_imbalance",
    "absolute_flip_imbalance",
    "paired_cross_flip_flow",
    "signed_flip_imbalance_fraction_of_paired_flow",
    "does_signed_flip_balance",
    "eta_signed_flip_by_p",
    "does_signed_flip_decay",
    "q_net_residue_proxy",
    "does_net_residue_decay",
    "no2cycle_candidate_count",
    "no2cycle_failure_count",
    "does_no2cycle_hold",
    "route_decision",
    "BT_distance_proxy",
    "classification_field_used_for_source_kind",
    "signed_source_summability_proved",
    "bt_signed_decay_theorem_proved",
    "net_residue_lyapunov_proved",
    "no_persistent_two_cycle_proved",
    "clay_promotion",
    "navier_stokes_promotion",
}

SPRINT52_MATERIAL_NO2CYCLE_REQUIRED_SUMMARY_FIELDS = {
    "contract",
    "diagnostic_mode",
    "source_true_new_material_total",
    "weighted_true_new_material_total",
    "sigma_true_new_material",
    "material_true_new_source_absent",
    "material_source_beats_half_derivative",
    "does_material_source_gate_close",
    "no2cycle_candidate_count",
    "no2cycle_proxy_failure_count",
    "no2cycle_amplitude_small_failure_count",
    "no2cycle_amplitude_small_failure_fraction",
    "weighted_no2cycle_amplitude_total",
    "does_no2cycle_amplitude_gate_close",
    "route_decision",
    "material_source_exponent_proved",
    "weighted_no2cycle_amplitude_summability_proved",
    "clay_promotion",
    "navier_stokes_promotion",
}

SPRINT53_NO2CYCLE_PHYSICAL_REQUIRED_SUMMARY_FIELDS = {
    "contract",
    "diagnostic_mode",
    "physical_no2cycle_row_count",
    "physical_amplitude_row_count",
    "no2cycle_candidate_count",
    "no2cycle_proxy_failure_count",
    "physical_no2cycle_failure_count",
    "physical_large_cycle_count",
    "physical_amplitude_small_failure_count",
    "physical_small_cycle_fraction",
    "physical_amplitude_small_failure_fraction",
    "weighted_physical_cycle_amplitude_total",
    "sigma_physical_cycle_fit",
    "does_physical_no2cycle_amplitude_gate_close",
    "does_physical_cycle_gate_close",
    "does_physical_cycle_summability_gate_close",
    "route_decision",
    "physical_no2cycle_amplitude_proved",
    "weighted_physical_no2cycle_amplitude_summability_proved",
    "physical_bridge_proved",
    "stretch_absorption_proved",
    "no_finite_time_blowup_proved",
    "clay_promotion",
    "navier_stokes_promotion",
}

SPRINT54_CYCLE_AMPLITUDE_REQUIRED_SUMMARY_FIELDS = {
    "contract",
    "diagnostic_mode",
    "cycle_amplitude_row_count",
    "cadence_comparison_row_count",
    "no2cycle_candidate_count",
    "no2cycle_proxy_failure_count",
    "physical_large_cycle_count",
    "physical_small_by_mass_count",
    "physical_small_by_mass_fraction",
    "physical_amplitude_small_majority",
    "small_fraction_by_stretch",
    "small_fraction_by_mass",
    "sigma_stretching_amplitude",
    "sigma_mass_amplitude",
    "cadence_sensitivity",
    "resolution_sensitivity",
    "direct_stretch_status",
    "direct_stretch_boundary",
    "shell_boundary_sensitivity",
    "does_no2cycle_cadence_gate_close",
    "does_no2cycle_resolution_gate_close",
    "does_direct_stretch_gate_close",
    "does_mass_proxy_gate_close",
    "route_decision",
    "no2cycle_aliasing_proved",
    "no2cycle_shell_boundary_artifact_proved",
    "no2cycle_proxy_overconservative_proved",
    "no2cycle_physical_obstruction_proved",
    "clay_promotion",
    "navier_stokes_promotion",
}

SPRINT55_LAGRANGIAN_ACTION_REQUIRED_SUMMARY_FIELDS = {
    "contract",
    "diagnostic_mode",
    "lagrangian_action_row_count",
    "hysteresis_row_count",
    "action_summary_row_count",
    "material_lineage_count",
    "direct_stretch_available_lineage_count",
    "action_threshold",
    "action_small_majority",
    "positive_action_total",
    "weighted_positive_action_total",
    "action_small_fraction",
    "dangerous_lineage_count",
    "sigma_action_fit",
    "does_lagrangian_action_gate_close",
    "does_lagrangian_action_summability_gate_close",
    "lagrangian_action_gate_proved",
    "weighted_action_summability_proved",
    "packet_local_stretch_action_available",
    "packet_local_stretch_action_proved",
    "color_string_proxy_demoted",
    "physical_bridge_proved",
    "stretch_absorption_proved",
    "no_finite_time_blowup_proved",
    "route_decision",
    "action_boundary",
    "direct_stretch_status",
    "clay_promotion",
    "navier_stokes_promotion",
}

SPRINT56_PACKET_LOCAL_ACTION_REQUIRED_SUMMARY_FIELDS = {
    "contract",
    "diagnostic_mode",
    "packet_local_action_row_count",
    "packet_local_hysteresis_row_count",
    "direction_change_row_count",
    "action_summary_row_count",
    "packet_local_available_lineage_count",
    "packet_local_available_fraction",
    "action_threshold",
    "action_small_majority",
    "redirection_threshold",
    "A_positive_total",
    "weighted_A_positive_total",
    "direction_change_integral_total",
    "redirection_without_overwhelm_count",
    "action_small_fraction",
    "dangerous_lineage_count",
    "sigma_packet_local_action_fit",
    "does_packet_local_action_gate_close",
    "does_packet_local_action_summability_gate_close",
    "packet_local_mask_reconstruction_available",
    "packet_local_action_gate_proved",
    "weighted_packet_local_action_summability_proved",
    "direction_change_separation_proved",
    "physical_bridge_proved",
    "stretch_absorption_proved",
    "no_finite_time_blowup_proved",
    "route_decision",
    "packet_local_boundary",
    "packet_local_status",
    "clay_promotion",
    "navier_stokes_promotion",
}

SPRINT57_VESSEL_ACTION_REQUIRED_SUMMARY_FIELDS = {
    "contract",
    "diagnostic_mode",
    "assignment_scheme",
    "time_window_count",
    "global_raw_positive_stretch_action_total",
    "global_raw_net_stretch_action_total",
    "covered_raw_positive_stretch_action_total",
    "covered_raw_net_stretch_action_total",
    "packet_raw_positive_stretch_action_total",
    "packet_raw_net_stretch_action_total",
    "global_normalized_positive_action_total",
    "global_normalized_net_action_total",
    "packet_normalized_positive_action_total",
    "packet_normalized_net_action_total",
    "epsilon_raw_positive_vs_global",
    "epsilon_raw_net_vs_global",
    "epsilon_raw_positive_vs_covered",
    "epsilon_raw_net_vs_covered",
    "epsilon_normalized_positive_vs_global",
    "epsilon_normalized_net_vs_global",
    "mean_coverage_fraction",
    "max_double_count_fraction",
    "reconstruction_tolerance",
    "dangerous_lineage_count",
    "sigma_packet_local_action_fit",
    "packet_local_action_gate_proved",
    "packet_action_reconstructs_global_stretch_proved",
    "ultrametric_reassignment_proved",
    "weighted_packet_local_action_summability_proved",
    "physical_bridge_proved",
    "stretch_absorption_proved",
    "no_finite_time_blowup_proved",
    "route_decision",
    "promotion_status",
    "receipt_alignment",
    "boundary",
    "clay_promotion",
    "navier_stokes_promotion",
}

SPRINT58_NORMALIZED_ACTION_INFLATION_REQUIRED_SUMMARY_FIELDS = {
    "contract",
    "diagnostic_mode",
    "time_window_count",
    "packet_inflation_row_count",
    "packet_normalized_positive_action_total",
    "covered_ratio_positive_action_total",
    "global_ratio_positive_action_total",
    "sum_ratios_over_ratio_of_sums_covered",
    "sum_ratios_over_ratio_of_sums_global",
    "packet_raw_positive_stretch_action_total",
    "covered_raw_positive_stretch_action_total",
    "global_raw_positive_stretch_action_total",
    "packet_enstrophy_total",
    "covered_enstrophy_total",
    "global_enstrophy_total",
    "low_enstrophy_denominator_count",
    "low_enstrophy_denominator_fraction",
    "inflation_candidate_count",
    "inflation_candidate_fraction",
    "max_packet_to_covered_ratio_inflation",
    "max_packet_to_global_ratio_inflation",
    "low_enstrophy_fraction_threshold",
    "inflation_factor_threshold",
    "packet_action_reconstruction_proved",
    "normalized_action_additivity_proved",
    "denominator_inflation_theorem_proved",
    "weighted_packet_action_summability_proved",
    "physical_bridge_proved",
    "stretch_absorption_proved",
    "no_finite_time_blowup_proved",
    "route_decision",
    "promotion_status",
    "receipt_alignment",
    "boundary",
    "clay_promotion",
    "navier_stokes_promotion",
}


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--truth", type=Path, default=None, help="truth NPZ containing omega_snapshots and steps")
    parser.add_argument(
        "--replay-packet-summary",
        type=Path,
        default=None,
        help="replay Sprint 48 replenishment decomposition from an existing ns_packet_transition_summary.csv",
    )
    parser.add_argument(
        "--replay-material-parent-summary",
        type=Path,
        default=None,
        help="replay Sprint 49 material-parent diagnostics from a GPU-produced ns_material_parent_summary.csv",
    )
    parser.add_argument(
        "--replay-ternary-cross-shell-summary",
        type=Path,
        default=None,
        help="replay Sprint 50 ternary cross-shell diagnostics from a GPU-produced ns_ternary_cross_shell_summary.json",
    )
    parser.add_argument(
        "--replay-signed-ternary-flip-summary",
        type=Path,
        default=None,
        help="replay Sprint 51 signed ternary flip diagnostics from a GPU-produced ns_signed_ternary_flip_summary.json",
    )
    parser.add_argument(
        "--replay-sprint52-material-no2cycle-summary",
        type=Path,
        default=None,
        help="replay Sprint 52 material source/no-2-cycle diagnostics from ns_sprint52_material_no2cycle_summary.json",
    )
    parser.add_argument(
        "--replay-sprint53-no2cycle-physical-summary",
        type=Path,
        default=None,
        help="replay Sprint 53 no-2-cycle physical amplitude diagnostics from ns_sprint53_no2cycle_summary.json",
    )
    parser.add_argument(
        "--replay-sprint54-cycle-amplitude-summary",
        type=Path,
        default=None,
        help="replay Sprint 54 no-2-cycle resolution/cadence diagnostics from ns_sprint54_cycle_amplitude_summary.json",
    )
    parser.add_argument(
        "--replay-sprint55-lagrangian-action-summary",
        type=Path,
        default=None,
        help="replay Sprint 55 Lagrangian accumulated stretch-action diagnostics from ns_sprint55_lagrangian_action_summary.json",
    )
    parser.add_argument(
        "--replay-sprint56-packet-local-action-summary",
        type=Path,
        default=None,
        help="replay Sprint 56 packet-local accumulated stretch-action diagnostics from ns_sprint56_packet_local_action_summary.json",
    )
    parser.add_argument(
        "--replay-sprint57-vessel-action-summary",
        type=Path,
        default=None,
        help="replay Sprint 57 global vessel/action reconciliation diagnostics from ns_sprint57_vessel_action_reconciliation_summary.json",
    )
    parser.add_argument(
        "--replay-sprint58-normalized-action-inflation-summary",
        type=Path,
        default=None,
        help="replay Sprint 58 normalized packet-action inflation diagnostics from ns_sprint58_normalized_action_inflation_summary.json",
    )
    parser.add_argument(
        "--ev5-dir",
        type=Path,
        default=None,
        help="optional dashiCFD EV5 output directory; resolves manifest source_truth and imports K* metadata",
    )
    parser.add_argument("--out-dir", type=Path, required=True, help="output directory")
    parser.add_argument("--smoke", action="store_true", help="run deterministic 3D smoke data instead of --truth")
    parser.add_argument("--smoke-n", type=int, default=16, help="3D smoke grid size")
    parser.add_argument("--smoke-samples", type=int, default=3, help="3D smoke sample count")
    parser.add_argument(
        "--diagnostic-backend",
        choices=["cpu", "gpu"],
        default="cpu",
        help="backend for 3D spectral diagnostic hot loops; gpu requires dashiCFD Vulkan/vkFFT support",
    )
    parser.add_argument(
        "--fft-backend",
        choices=["vkfft", "vkfft-vulkan"],
        default="vkfft-vulkan",
        help="GPU diagnostic FFT backend when --diagnostic-backend=gpu",
    )
    parser.add_argument(
        "--diagnostic-precision",
        choices=["float32", "float64"],
        default="float32",
        help="GPU diagnostic hot-loop precision; float64 is a parity/debug lane",
    )
    parser.add_argument(
        "--shell-convention",
        choices=["auto", "dyadic", "integer-radius"],
        default="auto",
        help="spectral shell projection convention; auto preserves EV5 dyadic shells and uses integer-radius for make_truth_3d artifacts",
    )
    parser.add_argument("--dt", type=float, default=None, help="override timestep")
    parser.add_argument("--nu", type=float, default=None, help="override viscosity")
    parser.add_argument("--theta", type=float, default=1.0, help="concentration penalty exponent")
    parser.add_argument(
        "--theta-grid",
        type=float,
        nargs="*",
        default=None,
        help="optional Sprint 43 residue-audit theta grid; defaults to --theta unless --residue-semantics-audit is set",
    )
    parser.add_argument("--p", type=int, default=3, help="prime lane used in budget_K")
    parser.add_argument("--residue-semantics-audit", action="store_true", help="emit Sprint 43 side-by-side Rplus semantics")
    parser.add_argument("--budget-component-audit", action="store_true", help="emit Sprint 45 source exponent budget audit")
    parser.add_argument("--source-decay-search", action="store_true", help="emit Sprint 46 source decay search diagnostics")
    parser.add_argument("--packet-lineage-audit", action="store_true", help="emit Sprint 47 coarse packet lineage diagnostics")
    parser.add_argument(
        "--replenishment-decomposition-audit",
        action="store_true",
        help="emit Sprint 48 packet replenishment source decomposition diagnostics",
    )
    parser.add_argument("--budget-threshold", type=float, default=0.5, help="source budget closure threshold")
    parser.add_argument(
        "--residue-key",
        choices=[
            "Rplus_strict",
            "Rplus_strain",
            "Rplus_stretchSign",
            "Rplus_pressureRelaxed",
            "Rplus_noPressure",
        ],
        default="Rplus_stretchSign",
        help="Sprint 45 residue/source observable used for gamma/eta fitting",
    )
    parser.add_argument(
        "--budget-primes",
        type=int,
        nargs="*",
        default=[2, 3, 5, 7, 11, 71],
        help="prime lanes to audit for eta-only and guarded independent budgets",
    )
    parser.add_argument("--coherence-threshold", type=float, default=0.65)
    parser.add_argument("--beltrami-threshold", type=float, default=0.15)
    parser.add_argument("--pressure-decorrelation-threshold", type=float, default=0.70)
    parser.add_argument(
        "--pressure-high-threshold",
        type=float,
        default=0.90,
        help="Sprint 44 pressure-relaxed downgrade threshold",
    )
    parser.add_argument("--eps", type=float, default=1e-12, help="diagnostic denominator epsilon")
    parser.add_argument(
        "--packet-grid",
        type=int,
        default=8,
        help="coarse spatial packets per axis for Sprint 47 packet-lineage proxy",
    )
    parser.add_argument(
        "--packet-active-quantile",
        type=float,
        default=0.90,
        help="quantile of shell enstrophy density used to activate coarse packet voxels",
    )
    parser.add_argument(
        "--packet-state-threshold",
        type=float,
        default=0.0,
        help="signed stretching ratio threshold for minus/zero/plus packet labels",
    )
    parser.add_argument(
        "--progress-every",
        type=int,
        default=0,
        help="print runtime progress every N shell rows while generating diagnostics; 0 disables progress",
    )
    return parser.parse_args()


def _load_meta(data: np.lib.npyio.NpzFile, dt_override: float | None) -> dict[str, Any]:
    meta: dict[str, Any] = {}
    if "meta_json" in data.files:
        raw = data["meta_json"]
        try:
            meta = json.loads(str(raw.item() if hasattr(raw, "item") else raw))
        except Exception:
            meta = {"meta_json_parse_error": True}
    if dt_override is not None:
        meta["dt"] = float(dt_override)
    meta.setdefault("dt", 1.0)
    return meta


def _effective_nu(meta: dict[str, Any], nu_override: float | None) -> float:
    if nu_override is not None:
        return float(nu_override)
    for key in ("nu0", "nu", "viscosity"):
        if key in meta and meta[key] is not None:
            return float(meta[key])
    return 1.0


def _synthetic_3d(samples: int, n: int, dt: float | None, nu: float | None) -> tuple[np.ndarray, np.ndarray, dict[str, Any]]:
    samples = max(1, int(samples))
    n = max(8, int(n))
    x = np.linspace(0.0, 2.0 * np.pi, n, endpoint=False)
    z, y, xg = np.meshgrid(x, x, x, indexing="ij")
    frames = []
    for s in range(samples):
        amp = math.exp(-0.08 * s)
        omega = np.empty((n, n, n, 3), dtype=np.float64)
        omega[..., 0] = amp * (np.sin(y) + 0.25 * np.cos(z + 0.2 * s))
        omega[..., 1] = amp * (np.sin(z) + 0.25 * np.cos(xg - 0.1 * s))
        omega[..., 2] = amp * (np.sin(xg) + 0.25 * np.cos(y + 0.3 * s))
        frames.append(omega)
    meta = {"source": "synthetic 3D smoke trace", "dt": 1.0 if dt is None else float(dt), "nu0": 0.01 if nu is None else float(nu)}
    return np.stack(frames, axis=0), np.arange(samples, dtype=np.int64), meta


def _load_truth(args: argparse.Namespace) -> tuple[np.ndarray, np.ndarray | None, np.ndarray, dict[str, Any], str]:
    if args.smoke:
        omega, steps, meta = _synthetic_3d(args.smoke_samples, args.smoke_n, args.dt, args.nu)
        return omega, None, steps, meta, "synthetic_3d_smoke"
    if args.ev5_dir is not None and args.truth is None:
        args.truth = _resolve_ev5_truth(args.ev5_dir)
    if args.truth is None:
        raise SystemExit("--truth is required unless --smoke is supplied")
    data = np.load(args.truth)
    if "omega_snapshots" not in data.files:
        raise SystemExit(f"{args.truth} lacks required key omega_snapshots")
    omega = np.asarray(data["omega_snapshots"], dtype=np.float64)
    velocity = None
    if "velocity_snapshots" in data.files:
        velocity = np.asarray(data["velocity_snapshots"], dtype=np.float64)
        if velocity.shape != omega.shape:
            raise SystemExit(
                f"{args.truth} velocity_snapshots shape {velocity.shape} does not match omega_snapshots shape {omega.shape}"
            )
    steps = np.asarray(data["steps"], dtype=np.int64) if "steps" in data.files else np.arange(omega.shape[0], dtype=np.int64)
    meta = _load_meta(data, args.dt)
    if args.ev5_dir is not None:
        ev5_meta = _load_ev5_manifest(args.ev5_dir)
        meta["ev5_dir"] = str(args.ev5_dir)
        if ev5_meta:
            meta["ev5_manifest"] = ev5_meta
            if args.nu is None and "nu" in ev5_meta:
                meta.setdefault("nu0", float(ev5_meta["nu"]))
            if args.dt is None and "dt" in ev5_meta:
                meta["dt"] = float(ev5_meta["dt"])
    return omega, velocity, steps, meta, str(args.truth)


def _load_ev5_manifest(ev5_dir: Path) -> dict[str, Any]:
    path = ev5_dir / "manifest.json"
    if not path.exists():
        return {}
    try:
        return json.loads(path.read_text(encoding="utf-8"))
    except Exception:
        return {"manifest_parse_error": True, "path": str(path)}


def _resolve_ev5_truth(ev5_dir: Path) -> Path:
    manifest = _load_ev5_manifest(ev5_dir)
    raw = manifest.get("source_truth")
    if not raw:
        raise SystemExit(f"{ev5_dir} lacks manifest source_truth; provide --truth explicitly")
    source = Path(str(raw))
    candidates = []
    if source.is_absolute():
        candidates.append(source)
    else:
        candidates.append(ev5_dir / source)
        for parent in ev5_dir.resolve().parents:
            candidates.append(parent / source)
    for candidate in candidates:
        if candidate.exists():
            return candidate
    raise SystemExit(f"could not resolve source_truth {raw!r} from {ev5_dir}")


def _frequencies(shape: tuple[int, ...]) -> tuple[np.ndarray, ...]:
    axes = [np.fft.fftfreq(n) * n for n in shape]
    return tuple(np.meshgrid(*axes, indexing="ij"))


def _dyadic_shells(shape: tuple[int, ...]) -> np.ndarray:
    grids = _frequencies(shape)
    radius_sq = np.zeros(shape, dtype=np.float64)
    for grid in grids:
        radius_sq += grid * grid
    radius = np.sqrt(radius_sq)
    shells = np.zeros(shape, dtype=np.int64)
    mask = radius >= 1.0
    shells[mask] = np.floor(np.log2(radius[mask])).astype(np.int64)
    return shells


def _integer_radius_shells(shape: tuple[int, ...]) -> np.ndarray:
    grids = _frequencies(shape)
    radius_sq = np.zeros(shape, dtype=np.float64)
    for grid in grids:
        radius_sq += grid * grid
    radius = np.sqrt(radius_sq)
    return np.floor(radius + 1e-12).astype(np.int64)


def _resolve_shell_convention(meta: dict[str, Any], args: argparse.Namespace, *, ndim: int) -> str:
    if args.shell_convention != "auto":
        return str(args.shell_convention)
    if ndim == 2:
        return "dyadic"
    if meta.get("source") == "synthetic 3D smoke trace":
        return "dyadic"
    if int(meta.get("dimension", 0) or 0) == 3 and (
        "k_star" in meta or meta.get("field") == "omega" or meta.get("projection") == "leray"
    ):
        return "integer-radius"
    return "dyadic"


def _shells_for_shape(shape: tuple[int, ...], meta: dict[str, Any], args: argparse.Namespace) -> tuple[np.ndarray, str]:
    convention = _resolve_shell_convention(meta, args, ndim=len(shape))
    if convention == "integer-radius":
        return _integer_radius_shells(shape), convention
    return _dyadic_shells(shape), convention


def _shell_filter_scalar(field: np.ndarray, shell_mask: np.ndarray) -> np.ndarray:
    hat = np.fft.fftn(field)
    return np.fft.ifftn(np.where(shell_mask, hat, 0.0)).real


def _shell_filter_vector(field: np.ndarray, shell_mask: np.ndarray) -> np.ndarray:
    return np.stack([_shell_filter_scalar(field[..., i], shell_mask) for i in range(field.shape[-1])], axis=-1)


def _l2_sq(field: np.ndarray) -> float:
    return float(np.mean(np.sum(field * field, axis=-1)))


def _curl_inverse_velocity(omega: np.ndarray) -> np.ndarray:
    shape = omega.shape[:-1]
    grids = _frequencies(shape)
    omega_hat = np.stack([np.fft.fftn(omega[..., i]) for i in range(3)], axis=-1)
    k = np.stack(grids, axis=-1).astype(np.float64)
    k2 = np.sum(k * k, axis=-1)
    k2_safe = np.where(k2 > 0.0, k2, 1.0)
    cross = np.cross(k, omega_hat)
    u_hat = 1j * cross / k2_safe[..., None]
    u_hat[k2 == 0.0] = 0.0
    return np.stack([np.fft.ifftn(u_hat[..., i]).real for i in range(3)], axis=-1)


def _grad_scalar(field: np.ndarray) -> list[np.ndarray]:
    shape = field.shape
    grids = _frequencies(shape)
    hat = np.fft.fftn(field)
    return [np.fft.ifftn(1j * grids[i] * hat).real for i in range(len(shape))]


def _strain_tensor(u: np.ndarray) -> np.ndarray:
    grads = [_grad_scalar(u[..., i]) for i in range(3)]
    shape = u.shape[:-1]
    strain = np.zeros(shape + (3, 3), dtype=np.float64)
    for i in range(3):
        for j in range(3):
            strain[..., i, j] = 0.5 * (grads[j][i] + grads[i][j])
    return strain


def _strain_tensor_from_derivatives(derivs: dict[tuple[int, int], np.ndarray], shape: tuple[int, int, int]) -> np.ndarray:
    strain = np.zeros(shape + (3, 3), dtype=np.float64)
    for i in range(3):
        for j in range(3):
            strain[..., i, j] = 0.5 * (np.asarray(derivs[(j, i)], dtype=np.float64) + np.asarray(derivs[(i, j)], dtype=np.float64))
    return strain


def _pressure_laplacian(u: np.ndarray) -> np.ndarray:
    grads = [_grad_scalar(u[..., i]) for i in range(3)]
    rhs = np.zeros(u.shape[:-1], dtype=np.float64)
    for i in range(3):
        for j in range(3):
            rhs -= grads[j][i] * grads[i][j]
    return rhs


def _pressure_laplacian_from_derivatives(derivs: dict[tuple[int, int], np.ndarray], shape: tuple[int, int, int]) -> np.ndarray:
    rhs = np.zeros(shape, dtype=np.float64)
    for i in range(3):
        for j in range(3):
            rhs -= np.asarray(derivs[(i, j)], dtype=np.float64) * np.asarray(derivs[(j, i)], dtype=np.float64)
    return rhs


def _coherence_defect(vectors: np.ndarray) -> float:
    mag = np.linalg.norm(vectors, axis=-1)
    active = mag > EPS
    if int(active.sum()) < 2:
        return 1.0
    dirs = vectors[active] / mag[active, None]
    cov = dirs.T @ dirs / float(dirs.shape[0])
    vals = np.linalg.eigvalsh(cov)
    coherence = float(vals[-1] / max(vals.sum(), EPS))
    return float(max(0.0, min(1.0, 1.0 - coherence)))


def _beltrami_defect(u: np.ndarray, omega: np.ndarray) -> float:
    u_norm = float(np.sqrt(np.mean(np.sum(u * u, axis=-1))))
    o_norm = float(np.sqrt(np.mean(np.sum(omega * omega, axis=-1))))
    if u_norm <= EPS or o_norm <= EPS:
        return 0.0
    cross_norm = float(np.sqrt(np.mean(np.sum(np.cross(u, omega) ** 2, axis=-1))))
    return float(max(0.0, min(1.0, cross_norm / (u_norm * o_norm + EPS))))


def _decorrelation_score(a: np.ndarray, h: np.ndarray) -> float:
    af = a.reshape(-1)
    hf = h.reshape(-1)
    af = af - float(af.mean())
    hf = hf - float(hf.mean())
    denom = float(np.linalg.norm(af) * np.linalg.norm(hf))
    if denom <= EPS:
        return 1.0
    corr = abs(float(np.dot(af, hf) / denom))
    return float(max(0.0, min(1.0, 1.0 - corr)))


def _concentration(omega: np.ndarray) -> float:
    density = np.sum(omega * omega, axis=-1)
    mean = float(np.mean(density))
    if mean <= EPS:
        return 0.0
    return float(np.max(density) / mean)


def _positive_stretch_share(stretch_density: np.ndarray) -> float:
    density = np.abs(stretch_density)
    total = float(np.sum(density))
    if total <= EPS:
        return 0.0
    return float(np.sum(np.maximum(stretch_density, 0.0)) / total)


_PACKET_GEOMETRY_CACHE: dict[tuple[tuple[int, ...], int], tuple[np.ndarray, np.ndarray]] = {}


def _packet_geometry(shape: tuple[int, int, int], packet_grid: int) -> tuple[np.ndarray, np.ndarray]:
    grid = max(1, int(packet_grid))
    key = (shape, grid)
    cached = _PACKET_GEOMETRY_CACHE.get(key)
    if cached is not None:
        return cached
    indices = np.indices(shape, dtype=np.int64)
    coarse = []
    coords = []
    for axis, size in enumerate(shape):
        coarse_axis = np.floor(indices[axis] * grid / max(size, 1)).astype(np.int64)
        coarse.append(np.clip(coarse_axis, 0, grid - 1))
        coords.append(indices[axis].astype(np.float64) / max(float(size), 1.0))
    lane_ids = coarse[0] * grid * grid + coarse[1] * grid + coarse[2]
    coord_stack = np.stack(coords, axis=-1)
    _PACKET_GEOMETRY_CACHE[key] = (lane_ids, coord_stack)
    return lane_ids, coord_stack


def _packet_state(signed_mass: float, abs_mass: float, threshold: float) -> str:
    if abs_mass <= EPS:
        return "zero"
    ratio = signed_mass / (abs_mass + EPS)
    cutoff = max(0.0, float(threshold))
    if ratio > cutoff:
        return "plus"
    if ratio < -cutoff:
        return "minus"
    return "zero"


def _direction_angle(a: np.ndarray | None, b: np.ndarray | None) -> float | None:
    if a is None or b is None:
        return None
    na = float(np.linalg.norm(a))
    nb = float(np.linalg.norm(b))
    if na <= EPS or nb <= EPS:
        return None
    cosine = float(np.dot(a, b) / (na * nb + EPS))
    cosine = max(-1.0, min(1.0, cosine))
    return float(math.acos(cosine))


def _packet_summaries(
    *,
    time: float,
    K: int,
    omega_k: np.ndarray,
    stretch_density: np.ndarray,
    args: argparse.Namespace,
) -> list[dict[str, Any]]:
    omega_sq = np.sum(omega_k * omega_k, axis=-1)
    positive_omega = omega_sq[omega_sq > EPS]
    if positive_omega.size == 0:
        return []
    quantile = max(0.0, min(1.0, float(args.packet_active_quantile)))
    active_threshold = float(np.quantile(positive_omega, quantile))
    active = omega_sq >= max(active_threshold, EPS)
    if not np.any(active):
        return []

    lane_ids, coords = _packet_geometry(tuple(omega_sq.shape), int(args.packet_grid))
    lane_flat = lane_ids[active].reshape(-1)
    coords_flat = coords[active].reshape(-1, 3)
    omega_flat = omega_k[active].reshape(-1, 3)
    omega_sq_flat = omega_sq[active].reshape(-1)
    stretch_flat = stretch_density[active].reshape(-1)
    abs_stretch_flat = np.abs(stretch_flat)
    use_stretch_mass = float(np.sum(abs_stretch_flat)) > EPS
    mass_flat = abs_stretch_flat if use_stretch_mass else omega_sq_flat

    packets: list[dict[str, Any]] = []
    for lane in np.unique(lane_flat):
        mask = lane_flat == lane
        mass = float(np.sum(mass_flat[mask]))
        if mass <= EPS:
            continue
        abs_mass = float(np.sum(abs_stretch_flat[mask]))
        signed_mass = float(np.sum(stretch_flat[mask]))
        weights = mass_flat[mask]
        centroid = np.average(coords_flat[mask], axis=0, weights=weights)
        direction_raw = np.sum(omega_flat[mask] * omega_sq_flat[mask, None], axis=0)
        direction_norm = float(np.linalg.norm(direction_raw))
        direction = direction_raw / direction_norm if direction_norm > EPS else np.zeros(3, dtype=np.float64)
        state = _packet_state(signed_mass, abs_mass, float(args.packet_state_threshold))
        lane_int = int(lane)
        packet_id = f"t{time:.12g}:K{int(K)}:lane{lane_int}"
        packets.append(
            {
                "time": float(time),
                "K": int(K),
                "packet_id": packet_id,
                "state": state,
                "mass": mass,
                "signed_stretch_mass": signed_mass,
                "abs_stretch_mass": abs_mass,
                "centroid": centroid,
                "direction": direction,
                "lane_int": lane_int,
                "BT_lane_id": f"eta_unavailable_coarse_spatial_lane_{lane_int}",
                "braid_word_id_proxy": f"coarse:{lane_int}:state:{state}",
            }
        )
    return packets


def _principal_positive_strain_residue(strain: np.ndarray, omega: np.ndarray) -> float:
    strain_residue, _ = _principal_strain_observables(strain, omega)
    return strain_residue


def _principal_strain_observables(strain: np.ndarray, omega: np.ndarray) -> tuple[float, float]:
    omega_sq = np.sum(omega * omega, axis=-1)
    total_omega = float(np.sum(omega_sq))
    if total_omega <= EPS:
        return 0.0, 0.0
    vals, vecs = np.linalg.eigh(strain)
    lam = vals[..., -1]
    principal = vecs[..., :, -1]
    omega_norm = np.sqrt(omega_sq)
    active = omega_norm > EPS
    alignment = np.zeros_like(omega_sq)
    if np.any(active):
        unit_omega = np.zeros_like(omega)
        unit_omega[active] = omega[active] / omega_norm[active, None]
        alignment = np.einsum("...i,...i->...", unit_omega, principal) ** 2
    angular_coherence = float(max(0.0, min(1.0, np.sum(alignment * omega_sq) / total_omega)))
    positive_weight = np.maximum(lam, 0.0) * omega_sq
    denom = float(np.sum(positive_weight))
    if denom <= EPS:
        return 0.0, angular_coherence
    strain_residue = float(max(0.0, min(1.0, np.sum(alignment * positive_weight) / denom)))
    return strain_residue, angular_coherence


def _angular_coherence(strain: np.ndarray, omega: np.ndarray) -> float:
    _, angular_coherence = _principal_strain_observables(strain, omega)
    return angular_coherence


def _classify_residue(
    stretch_density: np.ndarray,
    beltrami_defect: float,
    coherence_defect: float,
    pressure_decorrelation: float,
    *,
    beltrami_threshold: float,
    coherence_threshold: float,
    pressure_threshold: float,
) -> tuple[float, float, float]:
    density = np.abs(stretch_density)
    total = float(np.sum(density))
    if total <= EPS:
        return 0.0, 1.0, 0.0
    coherent = (1.0 - coherence_defect) >= coherence_threshold
    non_beltrami = beltrami_defect >= beltrami_threshold
    pressure_decorrelated = pressure_decorrelation >= pressure_threshold
    positive = stretch_density > 0.0
    if pressure_decorrelated:
        rminus = float(np.sum(density) / total)
        return rminus, 1.0 - rminus, 0.0
    if coherent and non_beltrami:
        rplus = float(np.sum(density[positive]) / total)
        rminus = float(np.sum(density[~positive]) / total)
        rzero = max(0.0, 1.0 - rplus - rminus)
        return rminus, rzero, rplus
    rminus = float(np.sum(density[~positive]) / total) if np.any(~positive) else 0.0
    return rminus, max(0.0, 1.0 - rminus), 0.0


def _residue_semantics(
    stretch_density: np.ndarray,
    strain_tensor: np.ndarray,
    omega_k: np.ndarray,
    beltrami_defect: float,
    coherence_defect: float,
    pressure_decorrelation: float,
    *,
    strict_rplus: float,
    beltrami_threshold: float,
    coherence_threshold: float,
    pressure_threshold: float,
    pressure_high_threshold: float,
    strain_residue: float | None = None,
) -> dict[str, tuple[float, str, str]]:
    density = np.abs(stretch_density)
    total = float(np.sum(density))
    if strain_residue is None:
        strain_residue = _principal_positive_strain_residue(strain_tensor, omega_k)
    if total <= EPS:
        return {
            "Rplus_strict": (strict_rplus, "proof_candidate_current", "zero stretching density"),
            "Rplus_strain": (strain_residue, "diagnostic_physical_strain", "zero signed stretching density"),
            "Rplus_stretchSign": (0.0, "diagnostic_sign_residue", "zero stretching density"),
            "Rplus_pressureRelaxed": (0.0, "diagnostic_pressure_relaxed", "zero stretching density"),
            "Rplus_noPressure": (0.0, "diagnostic_no_pressure", "zero stretching density"),
        }
    positive_mass = _positive_stretch_share(stretch_density)
    coherent = (1.0 - coherence_defect) >= coherence_threshold
    non_beltrami = beltrami_defect >= beltrami_threshold
    pressure_decorrelated = pressure_decorrelation >= pressure_threshold
    pressure_high_decorr = pressure_decorrelation > pressure_high_threshold
    pressure_relaxed = positive_mass if coherent and non_beltrami and not pressure_high_decorr else 0.0
    no_pressure = strain_residue if non_beltrami else 0.0
    note_bits = []
    if coherent:
        note_bits.append("coherent")
    else:
        note_bits.append("not_coherent")
    if non_beltrami:
        note_bits.append("non_beltrami")
    else:
        note_bits.append("beltrami_safe")
    if pressure_decorrelated:
        note_bits.append("pressure_decorrelated")
    else:
        note_bits.append("pressure_coupled")
    if pressure_high_decorr:
        note_bits.append("pressure_high_decorrelated")
    note = ",".join(note_bits)
    return {
        "Rplus_strict": (strict_rplus, "proof_candidate_current", note),
        "Rplus_strain": (
            strain_residue,
            "diagnostic_physical_strain",
            "principal positive-strain alignment; ignores braid and pressure gates",
        ),
        "Rplus_stretchSign": (
            positive_mass,
            "diagnostic_sign_residue",
            "direct positive signed stretching share; tautology-adjacent diagnostic",
        ),
        "Rplus_pressureRelaxed": (
            pressure_relaxed,
            "diagnostic_pressure_relaxed",
            "strict coherence/non-Beltrami gates; pressure downgrades only above high threshold",
        ),
        "Rplus_noPressure": (
            no_pressure,
            "diagnostic_no_pressure",
            "non-Beltrami positive-strain residue; pressure cannot downgrade red",
        ),
    }


def _finite_slope(xs: list[float], ys: list[float], default: float = 0.0) -> float:
    pairs = [(x, y) for x, y in zip(xs, ys) if math.isfinite(x) and math.isfinite(y) and y > 0.0]
    if len(pairs) < 2:
        return default
    x = np.asarray([p[0] for p in pairs], dtype=np.float64)
    y = np.log2(np.asarray([p[1] for p in pairs], dtype=np.float64))
    slope, _ = np.polyfit(x, y, 1)
    return float(slope)


def _progress(label: str, done: int, total: int, started: float, every: int) -> None:
    if every <= 0 or total <= 0:
        return
    if done < total and done % every != 0:
        return
    elapsed = time_module.perf_counter() - started
    rate = done / max(elapsed, 1e-12)
    remaining = max(0, total - done)
    eta = remaining / max(rate, 1e-12)
    print(
        f"[ns-harness] {label} progress={done}/{total} "
        f"elapsed={elapsed:.2f}s rate={rate:.2f} rows/s eta={eta:.2f}s",
        flush=True,
    )


def _rows_for_2d_scalar(
    omega: np.ndarray, steps: np.ndarray, meta: dict[str, Any], args: argparse.Namespace
) -> tuple[list[HarnessRow], dict[str, Any], list[dict[str, Any]]]:
    dt = float(meta.get("dt", 1.0))
    nu = _effective_nu(meta, args.nu)
    shells = _dyadic_shells(tuple(omega.shape[1:]))
    max_shell = int(shells.max())
    rows: list[HarnessRow] = []
    total = int(omega.shape[0]) * (max_shell + 1)
    started = time_module.perf_counter()
    done = 0
    for ti, frame in enumerate(omega):
        time = float(steps[ti]) * dt if ti < len(steps) else float(ti) * dt
        for k in range(max_shell + 1):
            mask = shells == k
            omega_k = _shell_filter_scalar(frame, mask)
            omega_l2 = float(np.mean(omega_k * omega_k))
            d_k = float(nu * (2.0 ** (2.0 * k)) * omega_l2)
            rows.append(
                HarnessRow(
                    K=k,
                    t=time,
                    omega_l2_sq=omega_l2,
                    D_K=d_k,
                    T_K=0.0,
                    Q_K=0.0,
                    Rminus_K=0.0,
                    Rzero_K=1.0,
                    Rplus_K=0.0,
                    netResidue_K=0.0,
                    BeltramiDefect_K=0.0,
                    DirectionCoherenceDefect_K=1.0,
                    PressureDecorrelationScore_K=1.0,
                    AlignedConcentration_K=float(np.max(omega_k * omega_k) / max(float(np.mean(omega_k * omega_k)), EPS)),
                    M_plus_minus=0.0,
                    M_plus_zero=0.0,
                    M_plus_plus=0.0,
                    s_K=0.0,
                    s_eff_K=0.0,
                    weighted_s_eff_K=0.0,
                    C_K=0.0,
                    gamma_K=0.0,
                    eta_K=0.0,
                    p=int(args.p),
                    beta_K=0.0,
                    theta=float(args.theta),
                    budget_K=0.0,
                    rho_K=0.0,
                    passBudget=0,
                    diagnostic_mode="2d_scalar_fail_closed_no_3d_stretching",
                )
            )
            done += 1
            _progress("2d", done, total, started, int(args.progress_every))
    summary = {
        "diagnostic_mode": "2d_scalar_fail_closed_no_3d_stretching",
        "physical_bridge_available": False,
        "reason": "input is 2D scalar vorticity; exact 3D vortex stretching is unavailable and the 2D embedded stretching term is zero",
        "evidence_only": True,
        "clay_promotion": False,
        "shell_convention": "dyadic",
        "velocity_source": "unavailable_2d_scalar",
    }
    return rows, summary, []


def _rows_for_3d_vector(
    omega: np.ndarray,
    velocity: np.ndarray | None,
    steps: np.ndarray,
    meta: dict[str, Any],
    args: argparse.Namespace,
) -> tuple[list[HarnessRow], dict[str, Any], list[dict[str, Any]]]:
    dt = float(meta.get("dt", 1.0))
    nu = _effective_nu(meta, args.nu)
    shells, shell_convention = _shells_for_shape(tuple(omega.shape[1:-1]), meta, args)
    max_shell = int(shells.max())
    preliminary: list[dict[str, Any]] = []
    total = int(omega.shape[0]) * (max_shell + 1)
    started = time_module.perf_counter()
    done = 0
    for ti, frame in enumerate(omega):
        time = float(steps[ti]) * dt if ti < len(steps) else float(ti) * dt
        u = velocity[ti] if velocity is not None else _curl_inverse_velocity(frame)
        pressure_lap = _pressure_laplacian(u)
        for k in range(max_shell + 1):
            mask = shells == k
            omega_k = _shell_filter_vector(frame, mask)
            u_k = _shell_filter_vector(u, mask)
            h_k = _shell_filter_scalar(pressure_lap, mask)
            s_k_tensor = _strain_tensor(u_k)
            s_omega = np.einsum("...ij,...j->...i", s_k_tensor, omega_k)
            stretch_density = np.einsum("...i,...i->...", s_omega, omega_k)
            packet_summaries = (
                _packet_summaries(
                    time=time,
                    K=k,
                    omega_k=omega_k,
                    stretch_density=stretch_density,
                    args=args,
                )
                if bool(args.packet_lineage_audit or args.replenishment_decomposition_audit)
                else []
            )
            t_k = abs(float(np.mean(stretch_density)))
            omega_l2 = _l2_sq(omega_k)
            d_k = float(nu * (2.0 ** (2.0 * k)) * omega_l2)
            q_k = float(t_k / (2.0 ** (0.5 * k) * d_k + float(args.eps)))
            beltrami = _beltrami_defect(u_k, omega_k)
            coherence_defect = _coherence_defect(omega_k)
            pressure_decorrelation = _decorrelation_score(stretch_density, h_k)
            concentration = _concentration(omega_k)
            strain_residue, angular_coherence = _principal_strain_observables(s_k_tensor, omega_k)
            rminus, rzero, rplus = _classify_residue(
                stretch_density,
                beltrami,
                coherence_defect,
                pressure_decorrelation,
                beltrami_threshold=float(args.beltrami_threshold),
                coherence_threshold=float(args.coherence_threshold),
                pressure_threshold=float(args.pressure_decorrelation_threshold),
            )
            c_k = float(q_k / (rplus * (concentration ** float(args.theta)) + float(args.eps)))
            semantic_values = _residue_semantics(
                stretch_density,
                s_k_tensor,
                omega_k,
                beltrami,
                coherence_defect,
                pressure_decorrelation,
                strict_rplus=rplus,
                beltrami_threshold=float(args.beltrami_threshold),
                coherence_threshold=float(args.coherence_threshold),
                pressure_threshold=float(args.pressure_decorrelation_threshold),
                pressure_high_threshold=float(args.pressure_high_threshold),
                strain_residue=strain_residue,
            )
            preliminary.append(
                {
                    "K": k,
                    "t": time,
                    "omega_l2_sq": omega_l2,
                    "D_K": d_k,
                    "T_K": t_k,
                    "Q_K": q_k,
                    "Rminus_K": rminus,
                    "Rzero_K": rzero,
                    "Rplus_K": rplus,
                    "netResidue_K": rplus - rminus,
                    "BeltramiDefect_K": beltrami,
                    "DirectionCoherenceDefect_K": coherence_defect,
                    "PressureDecorrelationScore_K": pressure_decorrelation,
                    "AngularCoherence_K": angular_coherence,
                    "AlignedConcentration_K": concentration,
                    "C_K": c_k,
                    "residue_semantics": semantic_values,
                    "packet_summaries": packet_summaries,
                }
            )
            done += 1
            _progress("3d", done, total, started, int(args.progress_every))

    by_time: dict[float, list[dict[str, Any]]] = {}
    for row in preliminary:
        by_time.setdefault(float(row["t"]), []).append(row)
    enriched: list[HarnessRow] = []
    for time, time_rows in by_time.items():
        time_rows.sort(key=lambda r: int(r["K"]))
        conc_slope = _finite_slope([float(r["K"]) for r in time_rows], [float(r["AlignedConcentration_K"]) for r in time_rows])
        rplus_slope = _finite_slope([float(r["K"]) for r in time_rows], [float(r["Rplus_K"]) + EPS for r in time_rows])
        beta = max(0.0, conc_slope)
        gamma = max(0.0, -rplus_slope)
        eta = 0.0
        for idx, row in enumerate(time_rows):
            k = int(row["K"])
            next_rplus = float(time_rows[idx + 1]["Rplus_K"]) if idx + 1 < len(time_rows) else 0.0
            rho = float(next_rplus / (float(row["Rplus_K"]) + float(args.eps)))
            mpp = rho
            s_k = max(0.0, next_rplus - mpp * float(row["Rplus_K"])) if idx + 1 < len(time_rows) else 0.0
            mpm = 0.0
            mpz = 0.0
            s_eff = mpm * float(row["Rminus_K"]) + mpz * float(row["Rzero_K"]) + s_k
            budget = gamma + eta * math.log2(float(args.p)) - float(args.theta) * beta
            enriched.append(
                HarnessRow(
                    K=k,
                    t=time,
                    omega_l2_sq=float(row["omega_l2_sq"]),
                    D_K=float(row["D_K"]),
                    T_K=float(row["T_K"]),
                    Q_K=float(row["Q_K"]),
                    Rminus_K=float(row["Rminus_K"]),
                    Rzero_K=float(row["Rzero_K"]),
                    Rplus_K=float(row["Rplus_K"]),
                    netResidue_K=float(row["netResidue_K"]),
                    BeltramiDefect_K=float(row["BeltramiDefect_K"]),
                    DirectionCoherenceDefect_K=float(row["DirectionCoherenceDefect_K"]),
                    PressureDecorrelationScore_K=float(row["PressureDecorrelationScore_K"]),
                    AlignedConcentration_K=float(row["AlignedConcentration_K"]),
                    M_plus_minus=mpm,
                    M_plus_zero=mpz,
                    M_plus_plus=mpp,
                    s_K=s_k,
                    s_eff_K=s_eff,
                    weighted_s_eff_K=float((2.0 ** (0.5 * k)) * s_eff),
                    C_K=float(row["C_K"]),
                    gamma_K=gamma,
                    eta_K=eta,
                    p=int(args.p),
                    beta_K=beta,
                    theta=float(args.theta),
                    budget_K=budget,
                    rho_K=rho,
                    passBudget=1 if budget > 0.5 else 0,
                    diagnostic_mode="3d_vector_direct_spectral",
                )
            )
    summary = {
        "diagnostic_mode": "3d_vector_direct_spectral",
        "physical_bridge_available": True,
        "transition_lineage_available": False,
        "transition_note": "M_plus_plus/rho and s_eff are shell-ratio diagnostics, not particle lineage estimates",
        "evidence_only": True,
        "clay_promotion": False,
        "shell_convention": shell_convention,
        "velocity_source": "velocity_snapshots" if velocity is not None else "curl_inverse_from_omega",
    }
    return enriched, summary, preliminary


def _rows_for_3d_vector_gpu(
    omega: np.ndarray,
    velocity: np.ndarray | None,
    steps: np.ndarray,
    meta: dict[str, Any],
    args: argparse.Namespace,
) -> tuple[list[HarnessRow], dict[str, Any], list[dict[str, Any]]]:
    if velocity is None:
        raise SystemExit(
            "--diagnostic-backend=gpu requires velocity_snapshots in the truth NPZ for this first GPU harness path"
        )
    root = Path(__file__).resolve().parents[2]
    candidates = [root / "dashiCFD", root.parent / "dashiCFD", Path("/home/c/Documents/code/dashiCFD")]
    cfd_root = next((path for path in candidates if (path / "vulkan_truth3d_backend.py").exists()), None)
    if cfd_root is None:
        raise SystemExit("--diagnostic-backend=gpu could not locate sibling dashiCFD/vulkan_truth3d_backend.py")
    if str(cfd_root) not in sys.path:
        sys.path.insert(0, str(cfd_root))
    try:
        from vulkan_truth3d_backend import VulkanSpectralDiagnostic3DBackend, VulkanTruth3DBackend  # type: ignore
    except Exception as exc:
        raise SystemExit(f"--diagnostic-backend=gpu could not import Vulkan diagnostic backend: {exc}") from exc

    dt = float(meta.get("dt", 1.0))
    nu = _effective_nu(meta, args.nu)
    shape = tuple(int(v) for v in omega.shape[1:-1])
    if len(set(shape)) != 1:
        raise SystemExit(f"--diagnostic-backend=gpu requires cubic 3D snapshots; got {shape}")
    n = int(shape[0])
    length = float(meta.get("domain_length", meta.get("length", 2.0 * math.pi)))
    shells, shell_convention = _shells_for_shape(shape, meta, args)
    max_shell = int(shells.max())
    preliminary: list[dict[str, Any]] = []
    total = int(omega.shape[0]) * (max_shell + 1)
    started = time_module.perf_counter()
    done = 0
    gpu_runtime: dict[str, Any] = {}
    gpu_device: dict[str, Any] = {}
    backend = None
    try:
        precision = str(args.diagnostic_precision)
        print(
            f"[ns-harness] diagnostic_backend=gpu requested fft_backend={args.fft_backend} "
            f"precision={precision}",
            flush=True,
        )
        print(f"[ns-harness] VK_ICD_FILENAMES={os.environ.get('VK_ICD_FILENAMES', '<unset>')}", flush=True)
        if precision == "float64":
            backend = VulkanSpectralDiagnostic3DBackend(
                n,
                length=length,
                fft_backend=str(args.fft_backend),
                precision="float64",
                timing_enabled=False,
            )
        else:
            backend = VulkanTruth3DBackend(
                n,
                dt=dt,
                nu0=nu,
                length=length,
                fft_backend=str(args.fft_backend),
                timing_enabled=False,
            )
        backend.set_shell_ids(shells)
        gpu_runtime = dict(backend.runtime_info())
        gpu_device = dict(backend.device_info())
        if gpu_runtime.get("fft_plan_backend") != "vulkan" or gpu_runtime.get("ifft_plan_backend") != "vulkan":
            raise SystemExit(f"--diagnostic-backend=gpu fell back from Vulkan vkFFT: {gpu_runtime}")
        print(
            "[ns-harness] diagnostic_backend=gpu active "
            f"fft_plan_backend={gpu_runtime.get('fft_plan_backend')} "
            f"device={gpu_device.get('device_name', '<unknown>')}",
            flush=True,
        )
        for ti, frame in enumerate(omega):
            time = float(steps[ti]) * dt if ti < len(steps) else float(ti) * dt
            field_dtype = np.float64 if str(args.diagnostic_precision) == "float64" else np.float32
            u = np.asarray(velocity[ti], dtype=field_dtype)
            backend.set_velocity_real(u)
            backend.set_omega_real(np.asarray(frame, dtype=field_dtype))
            # dashiCFD names kx/ky/kz physically; this harness's CPU path uses
            # raw NumPy array-axis order from _frequencies(shape).  Request that
            # axis convention explicitly for CPU/GPU diagnostic parity.
            axis_k_names = ("kz", "ky", "kx")
            full_derivs = backend.read_velocity_derivatives("u", k_names=axis_k_names)
            pressure_lap = _pressure_laplacian_from_derivatives(full_derivs, shape)
            for k in range(max_shell + 1):
                omega_k = np.asarray(backend.read_shell_vector("omega_hat", k, shell_convention), dtype=np.float64)
                u_k = np.asarray(backend.read_shell_vector("u", k, shell_convention), dtype=np.float64)
                h_k = np.asarray(backend.read_shell_scalar_from_real(pressure_lap, k, shell_convention), dtype=np.float64)
                shell_derivs = backend.read_shell_velocity_derivatives(k, shell_convention, k_names=axis_k_names)
                s_k_tensor = _strain_tensor_from_derivatives(shell_derivs, shape)
                s_omega = np.einsum("...ij,...j->...i", s_k_tensor, omega_k)
                stretch_density = np.einsum("...i,...i->...", s_omega, omega_k)
                packet_summaries = (
                    _packet_summaries(
                        time=time,
                        K=k,
                        omega_k=omega_k,
                        stretch_density=stretch_density,
                        args=args,
                    )
                    if bool(args.packet_lineage_audit or args.replenishment_decomposition_audit)
                    else []
                )
                t_k = abs(float(np.mean(stretch_density)))
                omega_l2 = _l2_sq(omega_k)
                d_k = float(nu * (2.0 ** (2.0 * k)) * omega_l2)
                q_k = float(t_k / (2.0 ** (0.5 * k) * d_k + float(args.eps)))
                beltrami = _beltrami_defect(u_k, omega_k)
                coherence_defect = _coherence_defect(omega_k)
                pressure_decorrelation = _decorrelation_score(stretch_density, h_k)
                concentration = _concentration(omega_k)
                strain_residue, angular_coherence = _principal_strain_observables(s_k_tensor, omega_k)
                rminus, rzero, rplus = _classify_residue(
                    stretch_density,
                    beltrami,
                    coherence_defect,
                    pressure_decorrelation,
                    beltrami_threshold=float(args.beltrami_threshold),
                    coherence_threshold=float(args.coherence_threshold),
                    pressure_threshold=float(args.pressure_decorrelation_threshold),
                )
                c_k = float(q_k / (rplus * (concentration ** float(args.theta)) + float(args.eps)))
                semantic_values = _residue_semantics(
                    stretch_density,
                    s_k_tensor,
                    omega_k,
                    beltrami,
                    coherence_defect,
                    pressure_decorrelation,
                    strict_rplus=rplus,
                    beltrami_threshold=float(args.beltrami_threshold),
                    coherence_threshold=float(args.coherence_threshold),
                    pressure_threshold=float(args.pressure_decorrelation_threshold),
                    pressure_high_threshold=float(args.pressure_high_threshold),
                    strain_residue=strain_residue,
                )
                preliminary.append(
                    {
                        "K": k,
                        "t": time,
                        "omega_l2_sq": omega_l2,
                        "D_K": d_k,
                        "T_K": t_k,
                        "Q_K": q_k,
                        "Rminus_K": rminus,
                        "Rzero_K": rzero,
                        "Rplus_K": rplus,
                        "netResidue_K": rplus - rminus,
                        "BeltramiDefect_K": beltrami,
                        "DirectionCoherenceDefect_K": coherence_defect,
                        "PressureDecorrelationScore_K": pressure_decorrelation,
                        "AngularCoherence_K": angular_coherence,
                        "AlignedConcentration_K": concentration,
                        "C_K": c_k,
                        "residue_semantics": semantic_values,
                        "packet_summaries": packet_summaries,
                    }
                )
                done += 1
                _progress("3d-gpu", done, total, started, int(args.progress_every))
    finally:
        if backend is not None:
            backend.close()

    by_time: dict[float, list[dict[str, Any]]] = {}
    for row in preliminary:
        by_time.setdefault(float(row["t"]), []).append(row)
    enriched: list[HarnessRow] = []
    for time, time_rows in by_time.items():
        time_rows.sort(key=lambda r: int(r["K"]))
        conc_slope = _finite_slope([float(r["K"]) for r in time_rows], [float(r["AlignedConcentration_K"]) for r in time_rows])
        rplus_slope = _finite_slope([float(r["K"]) for r in time_rows], [float(r["Rplus_K"]) + EPS for r in time_rows])
        beta = max(0.0, conc_slope)
        gamma = max(0.0, -rplus_slope)
        eta = 0.0
        for idx, row in enumerate(time_rows):
            k = int(row["K"])
            next_rplus = float(time_rows[idx + 1]["Rplus_K"]) if idx + 1 < len(time_rows) else 0.0
            rho = float(next_rplus / (float(row["Rplus_K"]) + float(args.eps)))
            mpp = rho
            s_k = max(0.0, next_rplus - mpp * float(row["Rplus_K"])) if idx + 1 < len(time_rows) else 0.0
            mpm = 0.0
            mpz = 0.0
            s_eff = mpm * float(row["Rminus_K"]) + mpz * float(row["Rzero_K"]) + s_k
            budget = gamma + eta * math.log2(float(args.p)) - float(args.theta) * beta
            enriched.append(
                HarnessRow(
                    K=k,
                    t=time,
                    omega_l2_sq=float(row["omega_l2_sq"]),
                    D_K=float(row["D_K"]),
                    T_K=float(row["T_K"]),
                    Q_K=float(row["Q_K"]),
                    Rminus_K=float(row["Rminus_K"]),
                    Rzero_K=float(row["Rzero_K"]),
                    Rplus_K=float(row["Rplus_K"]),
                    netResidue_K=float(row["netResidue_K"]),
                    BeltramiDefect_K=float(row["BeltramiDefect_K"]),
                    DirectionCoherenceDefect_K=float(row["DirectionCoherenceDefect_K"]),
                    PressureDecorrelationScore_K=float(row["PressureDecorrelationScore_K"]),
                    AlignedConcentration_K=float(row["AlignedConcentration_K"]),
                    M_plus_minus=mpm,
                    M_plus_zero=mpz,
                    M_plus_plus=mpp,
                    s_K=s_k,
                    s_eff_K=s_eff,
                    weighted_s_eff_K=float((2.0 ** (0.5 * k)) * s_eff),
                    C_K=float(row["C_K"]),
                    gamma_K=gamma,
                    eta_K=eta,
                    p=int(args.p),
                    beta_K=beta,
                    theta=float(args.theta),
                    budget_K=budget,
                    rho_K=rho,
                    passBudget=1 if budget > 0.5 else 0,
                    diagnostic_mode="3d_vector_gpu_spectral",
                )
            )
    summary = {
        "diagnostic_mode": "3d_vector_gpu_spectral",
        "diagnostic_backend": "gpu",
        "physical_bridge_available": True,
        "transition_lineage_available": False,
        "transition_note": "M_plus_plus/rho and s_eff are shell-ratio diagnostics, not particle lineage estimates",
        "evidence_only": True,
        "clay_promotion": False,
        "shell_convention": shell_convention,
        "velocity_source": "velocity_snapshots",
        "gpu_runtime": gpu_runtime,
        "gpu_device": gpu_device,
        "gpu_icd": os.environ.get("VK_ICD_FILENAMES"),
        "diagnostic_precision": str(args.diagnostic_precision),
        "gpu_derivative_axis_convention": "numpy_array_axis_order:kz,ky,kx",
        "gpu_shell_filter": "exact_cpu_shell_id_lut",
        "gpu_precision_boundary": (
            "GPU diagnostic hot loop uses fp64 Vulkan/vkFFT fields; CPU reductions remain fp64."
            if str(args.diagnostic_precision) == "float64"
            else "GPU diagnostic hot loop uses fp32 Vulkan/vkFFT fields; CPU reductions remain fp64."
        ),
    }
    return enriched, summary, preliminary


def _write_csv(path: Path, rows: Iterable[HarnessRow]) -> None:
    rows = list(rows)
    path.parent.mkdir(parents=True, exist_ok=True)
    with open(path, "w", newline="", encoding="utf-8") as handle:
        writer = csv.DictWriter(handle, fieldnames=list(HarnessRow.__dataclass_fields__.keys()))
        writer.writeheader()
        for row in rows:
            writer.writerow(row.__dict__)


def _fmt(value: float | str | None) -> str:
    if value is None:
        return ""
    if isinstance(value, str):
        return value
    if not math.isfinite(value):
        return ""
    return format(float(value), ".17g")


def _tail_k_star_from_meta(meta: dict[str, Any]) -> int | None:
    ev5_manifest = meta.get("ev5_manifest")
    if isinstance(ev5_manifest, dict):
        value = ev5_manifest.get("tail_k_star")
        if value is not None:
            try:
                return int(math.floor(float(value)))
            except Exception:
                return None
    if "k_star" in meta and meta["k_star"] is not None:
        try:
            return int(math.floor(float(meta["k_star"])))
        except Exception:
            return None
    return None


def _tail_k_star_source(meta: dict[str, Any]) -> str:
    ev5_manifest = meta.get("ev5_manifest")
    if isinstance(ev5_manifest, dict) and ev5_manifest.get("tail_k_star") is not None:
        return "ev5_manifest.tail_k_star"
    if meta.get("k_star") is not None:
        return "meta_json.k_star"
    return "default_zero"


def _bridge_budget_rows(rows: list[HarnessRow], meta: dict[str, Any]) -> tuple[list[BridgeBudgetRow], dict[str, Any]]:
    by_time: dict[float, list[HarnessRow]] = {}
    for row in rows:
        by_time.setdefault(float(row.t), []).append(row)
    times = sorted(by_time)
    tail_by_time_k: dict[tuple[float, int], float] = {}
    tail_d_by_time_k: dict[tuple[float, int], float] = {}
    max_shell = max((r.K for r in rows), default=-1)
    for time in times:
        time_rows = sorted(by_time[time], key=lambda r: r.K)
        for k in range(max_shell + 1):
            tail = [r for r in time_rows if r.K >= k]
            tail_by_time_k[(time, k)] = float(sum(r.omega_l2_sq for r in tail))
            tail_d_by_time_k[(time, k)] = float(sum(r.D_K for r in tail))

    physical = any(r.diagnostic_mode == "3d_vector_direct_spectral" for r in rows)
    k_star = _tail_k_star_from_meta(meta)
    if k_star is None:
        k_star = 0
    nonzero_high_shells = sorted({r.K for r in rows if r.K >= k_star and r.omega_l2_sq > EPS})
    high_shell_support_pass = len(nonzero_high_shells) >= 5
    dt_values = [b - a for a, b in zip(times, times[1:]) if b > a]
    default_dt = min(dt_values) if dt_values else float(meta.get("dt", 1.0))

    out: list[BridgeBudgetRow] = []
    for time_index, time in enumerate(times):
        time_rows = sorted(by_time[time], key=lambda r: r.K)
        next_time = times[time_index + 1] if time_index + 1 < len(times) else None
        for row in time_rows:
            tail = tail_by_time_k[(time, row.K)]
            tail_d = tail_d_by_time_k[(time, row.K)]
            theta_ns: float | None = None
            if next_time is not None and tail_d > EPS:
                dt = max(next_time - time, EPS)
                tail_next = tail_by_time_k.get((next_time, row.K), tail)
                theta_ns = abs(((tail_next - tail) / dt) + tail_d) / tail_d

            adjusted: float | None = None
            if row.Rplus_K > EPS and row.AlignedConcentration_K > EPS:
                adjusted = row.Q_K / (row.Rplus_K * (row.AlignedConcentration_K ** row.theta) + EPS)

            unavailable: list[str] = []
            field_status = "measured_direct_3d_spectral_proxy_lineage"
            if not physical:
                field_status = "blocked_no_3d_vortex_stretching"
                unavailable.append("input is 2D scalar vorticity; literal 3D omega dot grad(u) omega is unavailable")
            if theta_ns is None:
                unavailable.append("theta_NS_K unavailable on final sample or zero tail dissipation")
            if adjusted is None:
                if row.Rplus_K <= EPS:
                    unavailable.append("adjusted_bridge_ratio unavailable because R_plus_K_proxy is zero")
                elif row.AlignedConcentration_K <= EPS:
                    unavailable.append("adjusted_bridge_ratio unavailable because concentration is zero")
                else:
                    unavailable.append("adjusted_bridge_ratio unavailable")
            if not high_shell_support_pass:
                unavailable.append("fewer than five nonzero shells at or above K_star")

            if not physical:
                promotion = "NO_PROMOTION_BLOCKED_NO_3D_STRETCHING"
            elif not high_shell_support_pass:
                promotion = "NO_PROMOTION_HIGH_SHELL_SUPPORT_FAIL"
            elif row.budget_K <= 0.5:
                promotion = "NO_PROMOTION_BUDGET_FAIL"
            elif adjusted is None:
                promotion = "NO_PROMOTION_BRIDGE_RATIO_UNAVAILABLE"
            else:
                promotion = "NO_PROMOTION_DIAGNOSTIC_ONLY"

            step = int(round(time / max(default_dt, EPS)))
            out.append(
                BridgeBudgetRow(
                    step=step,
                    time=float(time),
                    K=int(row.K),
                    shell_enstrophy=float(row.omega_l2_sq),
                    tail_enstrophy=float(tail),
                    D_K=float(row.D_K),
                    theta_NS_K=_fmt(theta_ns),
                    Q_K_proxy=_fmt(row.Q_K),
                    R_plus_K_proxy=_fmt(row.Rplus_K),
                    aligned_concentration_K=_fmt(row.AlignedConcentration_K),
                    beta_hat_K=_fmt(row.beta_K),
                    gamma_hat_K=_fmt(row.gamma_K),
                    eta_hat_K=_fmt(row.eta_K),
                    budget_hat_K=_fmt(row.budget_K),
                    adjusted_bridge_ratio=_fmt(adjusted),
                    promotion_status=promotion,
                    field_status=field_status,
                    unavailable_reason="; ".join(unavailable),
                    diagnostic_mode=row.diagnostic_mode,
                )
            )

    ratios_by_time: dict[float, list[float]] = {}
    for row in out:
        if row.adjusted_bridge_ratio:
            ratios_by_time.setdefault(row.time, []).append(float(row.adjusted_bridge_ratio))
    ratio_increases = sum(
        1
        for values in ratios_by_time.values()
        for a, b in zip(values, values[1:])
        if b > a
    )
    summary = {
        "bridge_budget_table_available": True,
        "k_star": int(k_star),
        "k_star_source": _tail_k_star_source(meta),
        "nonzero_shells_at_or_above_k_star": nonzero_high_shells,
        "high_shell_support_pass": high_shell_support_pass,
        "adjusted_bridge_ratio_shell_increases": int(ratio_increases),
        "adjusted_bridge_ratio_growth_fail": bool(ratio_increases > 0),
        "bridge_ratio_status": "measured" if ratios_by_time else "unavailable_zero_rplus_or_concentration",
        "bridge_budget_field_contract": [
            "step",
            "time",
            "K",
            "shell_enstrophy",
            "tail_enstrophy",
            "D_K",
            "theta_NS_K",
            "Q_K_proxy",
            "R_plus_K_proxy",
            "aligned_concentration_K",
            "beta_hat_K",
            "gamma_hat_K",
            "eta_hat_K",
            "budget_hat_K",
            "adjusted_bridge_ratio",
            "promotion_status",
        ],
    }
    return out, summary


def _write_bridge_budget_csv(path: Path, rows: Iterable[BridgeBudgetRow]) -> None:
    rows = list(rows)
    path.parent.mkdir(parents=True, exist_ok=True)
    with open(path, "w", newline="", encoding="utf-8") as handle:
        writer = csv.DictWriter(handle, fieldnames=list(BridgeBudgetRow.__dataclass_fields__.keys()))
        writer.writeheader()
        for row in rows:
            writer.writerow(row.__dict__)


def _theta_grid(args: argparse.Namespace) -> list[float]:
    if args.theta_grid is not None and len(args.theta_grid) > 0:
        values = [float(v) for v in args.theta_grid]
    elif bool(args.residue_semantics_audit):
        values = [0.0, 0.25, 0.5, 1.0]
    else:
        values = [float(args.theta)]
    out: list[float] = []
    for value in values:
        if value not in out:
            out.append(value)
    return out


def _percentile(values: list[float], q: float) -> float | None:
    if not values:
        return None
    return float(np.percentile(np.asarray(values, dtype=np.float64), q))


def _interpret_semantic_summary(
    semantic: str,
    zero_rows: int,
    ratio_rows: int,
    rows: int,
    inf_budget: float | None,
) -> str:
    if zero_rows > 0:
        return "FAIL_ZERO_RPLUS_POSITIVE_Q"
    if ratio_rows < rows:
        return "FAIL_RATIO_UNAVAILABLE"
    if inf_budget is None or inf_budget <= 0.5:
        return "FAIL_BUDGET_BELOW_HALF"
    if semantic == "Rplus_strict":
        return "STRICT_DIAGNOSTIC_SURVIVES_OBSERVED_GRID"
    return "RELAXED_DIAGNOSTIC_SURVIVES_OBSERVED_GRID_NOT_PROOF"


def _residue_audit_rows(
    preliminary: list[dict[str, Any]],
    meta: dict[str, Any],
    args: argparse.Namespace,
) -> tuple[list[ResidueAuditRow], list[ResidueThetaSummaryRow], dict[str, Any]]:
    if not preliminary:
        return [], [], {
            "residue_semantics_audit_available": False,
            "residue_semantics": [],
            "residue_theta_grid": [],
            "residue_semantics_best": None,
        }

    by_time: dict[float, list[dict[str, Any]]] = {}
    for row in preliminary:
        by_time.setdefault(float(row["t"]), []).append(row)
    times = sorted(by_time)
    dt_values = [b - a for a, b in zip(times, times[1:]) if b > a]
    default_dt = min(dt_values) if dt_values else float(meta.get("dt", 1.0))

    semantics = sorted(
        {
            semantic
            for row in preliminary
            for semantic in dict(row.get("residue_semantics", {})).keys()
        }
    )
    theta_values = _theta_grid(args)
    per_semantic_slopes: dict[tuple[float, str], tuple[float, float]] = {}
    for time in times:
        time_rows = sorted(by_time[time], key=lambda r: int(r["K"]))
        xs = [float(r["K"]) for r in time_rows]
        conc_slope = _finite_slope(xs, [float(r["AlignedConcentration_K"]) for r in time_rows])
        beta = max(0.0, conc_slope)
        for semantic in semantics:
            rplus_values = []
            for row in time_rows:
                values = dict(row.get("residue_semantics", {}))
                value = values.get(semantic, (0.0, "", ""))[0]
                rplus_values.append(float(value) + EPS)
            rplus_slope = _finite_slope(xs, rplus_values)
            gamma = max(0.0, -rplus_slope)
            per_semantic_slopes[(time, semantic)] = (beta, gamma)

    out: list[ResidueAuditRow] = []
    for time in times:
        for row in sorted(by_time[time], key=lambda r: int(r["K"])):
            step = int(round(time / max(default_dt, EPS)))
            q_k = float(row["Q_K"])
            concentration = float(row["AlignedConcentration_K"])
            values = dict(row.get("residue_semantics", {}))
            for semantic in semantics:
                rplus, status, note = values.get(semantic, (0.0, "unavailable", "semantic unavailable"))
                rplus = float(rplus)
                beta, gamma = per_semantic_slopes[(time, semantic)]
                for theta in theta_values:
                    budget = gamma - float(theta) * beta
                    zero_r_positive_q = int(rplus <= float(args.eps) and q_k > float(args.eps))
                    adjusted = None
                    if not zero_r_positive_q and rplus > EPS and concentration > EPS:
                        adjusted = q_k / (rplus * (concentration ** float(theta)) + EPS)
                    promotion = "NO_PROMOTION_RESIDUE_SEMANTICS_AUDIT"
                    if zero_r_positive_q:
                        promotion = "NO_PROMOTION_ZERO_RPLUS_POSITIVE_Q"
                    elif budget <= 0.5:
                        promotion = "NO_PROMOTION_BUDGET_FAIL"
                    elif adjusted is None:
                        promotion = "NO_PROMOTION_BRIDGE_RATIO_UNAVAILABLE"
                    elif status != "proof_candidate_current":
                        promotion = "NO_PROMOTION_SEMANTIC_NOT_PROOF_BOUNDARY"
                    out.append(
                        ResidueAuditRow(
                            step=step,
                            time=float(time),
                            K=int(row["K"]),
                            theta=float(theta),
                            semantic=semantic,
                            semantic_status=status,
                            Q_K=_fmt(q_k),
                            aligned_concentration_K=_fmt(concentration),
                            R_plus_K=_fmt(rplus),
                            adjusted_bridge_ratio=_fmt(adjusted),
                            beta_hat_K=_fmt(beta),
                            gamma_hat_K=_fmt(gamma),
                            eta_hat_K=_fmt(0.0),
                            budget_hat_K=_fmt(budget),
                            zeroR_positiveQ=zero_r_positive_q,
                            ratio_available=1 if adjusted is not None else 0,
                            budget_pass=1 if budget > 0.5 else 0,
                            promotion_status=promotion,
                            note=str(note),
                        )
                    )

    theta_summary_rows: list[ResidueThetaSummaryRow] = []
    semantic_summary: dict[str, dict[str, Any]] = {}
    for theta in theta_values:
        for semantic in semantics:
            rows = [r for r in out if r.semantic == semantic and abs(r.theta - float(theta)) <= EPS]
            ratios = [float(r.adjusted_bridge_ratio) for r in rows if r.adjusted_bridge_ratio]
            budgets = [float(r.budget_hat_K) for r in rows if r.budget_hat_K]
            inf_budget = min(budgets) if budgets else None
            interpretation = _interpret_semantic_summary(
                semantic,
                sum(r.zeroR_positiveQ for r in rows),
                sum(r.ratio_available for r in rows),
                len(rows),
                inf_budget,
            )
            promotion = "NO_PROMOTION_RESIDUE_SEMANTICS_AUDIT"
            if interpretation.startswith("FAIL_ZERO"):
                promotion = "NO_PROMOTION_ZERO_RPLUS_POSITIVE_Q"
            elif interpretation.startswith("FAIL_RATIO"):
                promotion = "NO_PROMOTION_BRIDGE_RATIO_UNAVAILABLE"
            elif interpretation.startswith("FAIL_BUDGET"):
                promotion = "NO_PROMOTION_BUDGET_FAIL"
            elif semantic != "Rplus_strict":
                promotion = "NO_PROMOTION_SEMANTIC_NOT_PROOF_BOUNDARY"
            theta_summary_rows.append(
                ResidueThetaSummaryRow(
                    theta=float(theta),
                    semantic=semantic,
                    semantic_status=rows[0].semantic_status if rows else "unavailable",
                    rows=len(rows),
                    ratio_available_rows=sum(r.ratio_available for r in rows),
                    zeroR_positiveQ_rows=sum(r.zeroR_positiveQ for r in rows),
                    budget_pass_rows=sum(r.budget_pass for r in rows),
                    sup_adjusted_bridge_ratio=_fmt(max(ratios) if ratios else None),
                    median_adjusted_bridge_ratio=_fmt(_percentile(ratios, 50.0)),
                    p95_adjusted_bridge_ratio=_fmt(_percentile(ratios, 95.0)),
                    inf_budget_hat_K=_fmt(inf_budget),
                    all_budget_pass=1 if budgets and min(budgets) > 0.5 else 0,
                    all_ratios_available=1 if rows and all(r.ratio_available for r in rows) else 0,
                    interpretation=interpretation,
                    promotion_status=promotion,
                )
            )

    for semantic in semantics:
        rows = [r for r in out if r.semantic == semantic]
        ratios = [float(r.adjusted_bridge_ratio) for r in rows if r.adjusted_bridge_ratio]
        budgets = [float(r.budget_hat_K) for r in rows if r.budget_hat_K]
        semantic_summary[semantic] = {
            "semantic_status": rows[0].semantic_status if rows else "unavailable",
            "rows": len(rows),
            "ratio_available_rows": sum(r.ratio_available for r in rows),
            "zeroR_positiveQ_rows": sum(r.zeroR_positiveQ for r in rows),
            "budget_pass_rows": sum(r.budget_pass for r in rows),
            "sup_adjusted_bridge_ratio": max(ratios) if ratios else None,
            "median_adjusted_bridge_ratio": _percentile(ratios, 50.0),
            "p95_adjusted_bridge_ratio": _percentile(ratios, 95.0),
            "inf_budget_hat_K": min(budgets) if budgets else None,
            "all_budget_pass": bool(budgets and min(budgets) > 0.5),
            "all_ratios_available": bool(rows and all(r.ratio_available for r in rows)),
        }

    best = None
    finite_candidates = [
        (name, data)
        for name, data in semantic_summary.items()
        if data["sup_adjusted_bridge_ratio"] is not None
        and math.isfinite(float(data["sup_adjusted_bridge_ratio"]))
    ]
    if finite_candidates:
        best = min(finite_candidates, key=lambda item: float(item[1]["sup_adjusted_bridge_ratio"]))[0]

    summary = {
        "residue_semantics_audit_available": True,
        "residue_semantics": semantics,
        "residue_theta_grid": theta_values,
        "residue_semantics_summary": semantic_summary,
        "residue_theta_grid_summary": [row.__dict__ for row in theta_summary_rows],
        "residue_semantics_best": best,
        "residue_semantics_promotes": False,
        "residue_semantics_boundary": (
            "Side-by-side R_plus definitions are diagnostic unless separately proved; "
            "no semantic can promote without budget > 1/2, bridge ratio availability, "
            "actual lineage, stretch absorption, and no-blowup proof."
        ),
    }
    return out, theta_summary_rows, summary


def _write_residue_audit_csv(path: Path, rows: Iterable[ResidueAuditRow]) -> None:
    rows = list(rows)
    path.parent.mkdir(parents=True, exist_ok=True)
    with open(path, "w", newline="", encoding="utf-8") as handle:
        writer = csv.DictWriter(handle, fieldnames=list(ResidueAuditRow.__dataclass_fields__.keys()))
        writer.writeheader()
        for row in rows:
            writer.writerow(row.__dict__)


def _write_residue_theta_summary_csv(path: Path, rows: Iterable[ResidueThetaSummaryRow]) -> None:
    rows = list(rows)
    path.parent.mkdir(parents=True, exist_ok=True)
    with open(path, "w", newline="", encoding="utf-8") as handle:
        writer = csv.DictWriter(handle, fieldnames=list(ResidueThetaSummaryRow.__dataclass_fields__.keys()))
        writer.writeheader()
        for row in rows:
            writer.writerow(row.__dict__)


def _write_residue_wide_csv(path: Path, rows: Iterable[ResidueAuditRow]) -> list[ResidueWideRow]:
    grouped: dict[tuple[int, float, int, float], dict[str, ResidueAuditRow]] = {}
    for row in rows:
        grouped.setdefault((row.step, row.time, row.K, row.theta), {})[row.semantic] = row
    wide_rows: list[ResidueWideRow] = []
    for key, semantic_rows in sorted(grouped.items()):
        step, time, k, theta = key
        exemplar = next(iter(semantic_rows.values()))

        def value(semantic: str, attr: str) -> str:
            row = semantic_rows.get(semantic)
            return "" if row is None else str(getattr(row, attr))

        def flag(semantic: str) -> int:
            row = semantic_rows.get(semantic)
            return 0 if row is None else int(row.zeroR_positiveQ)

        wide_rows.append(
            ResidueWideRow(
                step=step,
                time=time,
                K=k,
                theta=theta,
                Q_K=exemplar.Q_K,
                Conc_K=exemplar.aligned_concentration_K,
                Rplus_strict=value("Rplus_strict", "R_plus_K"),
                Rplus_strain=value("Rplus_strain", "R_plus_K"),
                Rplus_stretchSign=value("Rplus_stretchSign", "R_plus_K"),
                Rplus_pressureRelaxed=value("Rplus_pressureRelaxed", "R_plus_K"),
                Rplus_noPressure=value("Rplus_noPressure", "R_plus_K"),
                C_strict=value("Rplus_strict", "adjusted_bridge_ratio"),
                C_strain=value("Rplus_strain", "adjusted_bridge_ratio"),
                C_stretchSign=value("Rplus_stretchSign", "adjusted_bridge_ratio"),
                C_pressureRelaxed=value("Rplus_pressureRelaxed", "adjusted_bridge_ratio"),
                C_noPressure=value("Rplus_noPressure", "adjusted_bridge_ratio"),
                zeroR_positiveQ_strict=flag("Rplus_strict"),
                zeroR_positiveQ_strain=flag("Rplus_strain"),
                zeroR_positiveQ_stretchSign=flag("Rplus_stretchSign"),
                zeroR_positiveQ_pressureRelaxed=flag("Rplus_pressureRelaxed"),
                zeroR_positiveQ_noPressure=flag("Rplus_noPressure"),
            )
        )
    path.parent.mkdir(parents=True, exist_ok=True)
    with open(path, "w", newline="", encoding="utf-8") as handle:
        writer = csv.DictWriter(handle, fieldnames=list(ResidueWideRow.__dataclass_fields__.keys()))
        writer.writeheader()
        for row in wide_rows:
            writer.writerow(row.__dict__)
    return wide_rows


def _budget_component_audit_rows(
    preliminary: list[dict[str, Any]],
    meta: dict[str, Any],
    args: argparse.Namespace,
) -> tuple[list[BudgetComponentAuditRow], dict[str, Any]]:
    if not bool(args.budget_component_audit):
        return [], {
            "budget_component_audit_available": False,
            "budget_component_promotes": False,
        }
    if not preliminary:
        return [], {
            "budget_component_audit_available": False,
            "budget_component_promotes": False,
            "budget_component_unavailable_reason": "no 3d residue preliminary rows available",
        }

    residue_key = str(args.residue_key)
    theta_values = _theta_grid(args)
    primes = [int(p) for p in getattr(args, "budget_primes", []) if int(p) > 1]
    if not primes:
        primes = [int(args.p)] if int(args.p) > 1 else [2]

    by_time: dict[float, list[dict[str, Any]]] = {}
    for row in preliminary:
        by_time.setdefault(float(row["t"]), []).append(row)
    times = sorted(by_time)
    dt_values = [b - a for a, b in zip(times, times[1:]) if b > a]
    default_dt = min(dt_values) if dt_values else float(meta.get("dt", 1.0))

    out: list[BudgetComponentAuditRow] = []
    threshold = float(args.budget_threshold)
    for time in times:
        time_rows = sorted(by_time[time], key=lambda r: int(r["K"]))
        xs = [float(r["K"]) for r in time_rows]
        concentrations = [float(r["AlignedConcentration_K"]) for r in time_rows]
        beta = max(0.0, _finite_slope(xs, concentrations))
        source_values: list[float] = []
        for row in time_rows:
            semantics = dict(row.get("residue_semantics", {}))
            source, _, _ = semantics.get(residue_key, (0.0, "unavailable", "semantic unavailable"))
            source_values.append(float(source))
        gamma = max(0.0, -_finite_slope(xs, [value + EPS for value in source_values]))
        step = int(round(float(time) / max(default_dt, EPS)))

        for row, source in zip(time_rows, source_values):
            q_k = float(row["Q_K"])
            concentration = float(row["AlignedConcentration_K"])
            zero_r_positive_q = source <= float(args.eps) and q_k > float(args.eps)
            for theta in theta_values:
                gamma_budget_without_conc = gamma
                gamma_budget_with_conc = gamma - float(theta) * beta
                for prime in primes:
                    log2p = math.log2(float(prime))
                    eta = gamma / max(log2p, EPS)
                    eta_log2p = eta * log2p
                    budget_eta_only = eta_log2p - float(theta) * beta
                    budget_independent = gamma + eta_log2p - float(theta) * beta
                    gap_gamma = threshold - gamma_budget_with_conc
                    gap_eta = threshold - budget_eta_only
                    gap_independent = threshold - budget_independent
                    if zero_r_positive_q:
                        budget_status = "FAIL_ZERO_RPLUS_POSITIVE_Q"
                        promotion = "NO_PROMOTION_ZERO_RPLUS_POSITIVE_Q"
                    elif gamma_budget_with_conc > threshold:
                        budget_status = "PASS_GAMMA_ONLY_OBSERVED"
                        promotion = "NO_PROMOTION_BUDGET_COMPONENT_DIAGNOSTIC_ONLY"
                    elif budget_eta_only > threshold:
                        budget_status = "PASS_ETA_ONLY_SAME_OBSERVABLE"
                        promotion = "NO_PROMOTION_DOUBLE_COUNT_GUARD"
                    elif budget_independent > threshold:
                        budget_status = "COUNTERFACTUAL_INDEPENDENT_GAMMA_ETA_PASS"
                        promotion = "NO_PROMOTION_INDEPENDENCE_UNPROVED"
                    else:
                        budget_status = "FAIL_BUDGET_BELOW_HALF"
                        promotion = "NO_PROMOTION_BUDGET_FAIL"

                    out.append(
                        BudgetComponentAuditRow(
                            step=step,
                            time=float(time),
                            K=int(row["K"]),
                            theta=float(theta),
                            residue_key=residue_key,
                            p=int(prime),
                            Q_K=_fmt(q_k),
                            source_K=_fmt(source),
                            aligned_concentration_K=_fmt(concentration),
                            beta_fit=_fmt(beta),
                            gamma_fit=_fmt(gamma),
                            eta_fit=_fmt(eta),
                            eta_log2p_fit=_fmt(eta_log2p),
                            budget_without_concentration_gamma_only=_fmt(gamma_budget_without_conc),
                            budget_with_concentration_gamma_only=_fmt(gamma_budget_with_conc),
                            budget_if_gamma_only=_fmt(gamma_budget_with_conc),
                            budget_if_eta_only=_fmt(budget_eta_only),
                            budget_if_independent_gamma_eta=_fmt(budget_independent),
                            budget_gap_gamma_only=_fmt(gap_gamma),
                            budget_gap_eta_only=_fmt(gap_eta),
                            budget_gap_independent_gamma_eta=_fmt(gap_independent),
                            same_observable_gamma_eta=1,
                            independent_gamma_eta=0,
                            double_count_warning=(
                                "gamma and eta are inferred from the same residue observable; "
                                "budget_if_independent_gamma_eta is a counterfactual and cannot promote"
                            ),
                            budget_status=budget_status,
                            promotion_status=promotion,
                            note=(
                                "source_K is the selected residue observable; an independent BT lane "
                                "must be supplied before gamma and eta may be added"
                            ),
                        )
                    )

    gaps_gamma = [float(r.budget_gap_gamma_only) for r in out if r.budget_gap_gamma_only]
    gaps_eta = [float(r.budget_gap_eta_only) for r in out if r.budget_gap_eta_only]
    gaps_independent = [float(r.budget_gap_independent_gamma_eta) for r in out if r.budget_gap_independent_gamma_eta]
    budgets_gamma = [threshold - value for value in gaps_gamma]
    budgets_eta = [threshold - value for value in gaps_eta]
    budgets_independent = [threshold - value for value in gaps_independent]
    status_counts: dict[str, int] = {}
    for row in out:
        status_counts[row.budget_status] = status_counts.get(row.budget_status, 0) + 1
    eta_by_p: dict[str, dict[str, Any]] = {}
    for prime in sorted({row.p for row in out}):
        rows_for_prime = [row for row in out if row.p == prime]
        eta_values = [float(row.eta_fit) for row in rows_for_prime if row.eta_fit]
        eta_log2p_values = [float(row.eta_log2p_fit) for row in rows_for_prime if row.eta_log2p_fit]
        eta_by_p[str(prime)] = {
            "eta_fit_min": min(eta_values) if eta_values else None,
            "eta_fit_max": max(eta_values) if eta_values else None,
            "eta_log2p_fit_min": min(eta_log2p_values) if eta_log2p_values else None,
            "eta_log2p_fit_max": max(eta_log2p_values) if eta_log2p_values else None,
            "same_observable_as_gamma": True,
        }

    summary = {
        "budget_component_audit_available": True,
        "budget_component_residue_key": residue_key,
        "budget_component_primes": primes,
        "budget_component_theta_grid": theta_values,
        "budget_component_threshold": threshold,
        "budget_component_row_count": len(out),
        "gamma_fit_min": min((float(r.gamma_fit) for r in out if r.gamma_fit), default=None),
        "gamma_fit_max": max((float(r.gamma_fit) for r in out if r.gamma_fit), default=None),
        "beta_fit_min": min((float(r.beta_fit) for r in out if r.beta_fit), default=None),
        "beta_fit_max": max((float(r.beta_fit) for r in out if r.beta_fit), default=None),
        "eta_fit_by_p": eta_by_p,
        "inf_budget_if_gamma_only": min(budgets_gamma) if budgets_gamma else None,
        "inf_budget_if_eta_only": min(budgets_eta) if budgets_eta else None,
        "inf_budget_if_independent_gamma_eta": min(budgets_independent) if budgets_independent else None,
        "sup_budget_gap_gamma_only": max(gaps_gamma) if gaps_gamma else None,
        "sup_budget_gap_eta_only": max(gaps_eta) if gaps_eta else None,
        "sup_budget_gap_independent_gamma_eta": max(gaps_independent) if gaps_independent else None,
        "budget_component_status_counts": status_counts,
        "double_count_warning": (
            "eta_fit_by_p is converted from the same source slope as gamma_fit; "
            "do not add gamma and eta*log2(p) without an independent observable."
        ),
        "budget_component_promotes": False,
        "budget_component_boundary": (
            "Sprint 45 audits gamma/eta/beta components only. It does not prove "
            "independent DASHI source decay, actual ternary lineage, stretch absorption, "
            "no finite-time blowup, or Clay Navier-Stokes regularity."
        ),
        "budget_component_field_contract": list(BudgetComponentAuditRow.__dataclass_fields__.keys()),
    }
    return out, summary


def _write_budget_component_audit_csv(path: Path, rows: Iterable[BudgetComponentAuditRow]) -> None:
    rows = list(rows)
    path.parent.mkdir(parents=True, exist_ok=True)
    with open(path, "w", newline="", encoding="utf-8") as handle:
        writer = csv.DictWriter(handle, fieldnames=list(BudgetComponentAuditRow.__dataclass_fields__.keys()))
        writer.writeheader()
        for row in rows:
            writer.writerow(row.__dict__)


def _source_decay_search_rows(
    preliminary: list[dict[str, Any]],
    meta: dict[str, Any],
    args: argparse.Namespace,
) -> tuple[list[SourceDecaySearchRow], dict[str, Any]]:
    if not bool(args.source_decay_search):
        return [], {
            "source_decay_search_available": False,
            "source_decay_search_promotes": False,
        }
    if not preliminary:
        return [], {
            "source_decay_search_available": False,
            "source_decay_search_promotes": False,
            "source_decay_unavailable_reason": "no 3d residue preliminary rows available",
        }

    residue_key = str(args.residue_key)
    theta_values = _theta_grid(args)
    threshold = float(args.budget_threshold)
    rho_threshold = 1.0 / math.sqrt(2.0)
    by_time: dict[float, list[dict[str, Any]]] = {}
    for row in preliminary:
        by_time.setdefault(float(row["t"]), []).append(row)
    times = sorted(by_time)
    dt_values = [b - a for a, b in zip(times, times[1:]) if b > a]
    default_dt = min(dt_values) if dt_values else float(meta.get("dt", 1.0))

    out: list[SourceDecaySearchRow] = []
    for time in times:
        time_rows = sorted(by_time[time], key=lambda r: int(r["K"]))
        xs = [float(r["K"]) for r in time_rows]
        rplus_values: list[float] = []
        for row in time_rows:
            semantics = dict(row.get("residue_semantics", {}))
            rplus, _, _ = semantics.get(residue_key, (0.0, "unavailable", "semantic unavailable"))
            rplus_values.append(float(rplus))
        angular_values = [float(row.get("AngularCoherence_K", 0.0)) for row in time_rows]
        pressure_survival_values = [
            max(0.0, 1.0 - float(row["PressureDecorrelationScore_K"]))
            for row in time_rows
        ]
        concentration_values = [float(row["AlignedConcentration_K"]) for row in time_rows]
        angular_sigma = max(0.0, -_finite_slope(xs, [value + EPS for value in angular_values]))
        pressure_sigma = max(0.0, -_finite_slope(xs, [value + EPS for value in pressure_survival_values]))
        beta = max(0.0, _finite_slope(xs, concentration_values))
        step = int(round(float(time) / max(default_dt, EPS)))

        for idx, (row, rplus) in enumerate(zip(time_rows, rplus_values)):
            next_rplus = rplus_values[idx + 1] if idx + 1 < len(rplus_values) else None
            rho = None
            if next_rplus is not None and rplus > float(args.eps):
                rho = next_rplus / (rplus + float(args.eps))
            for theta in theta_values:
                angular_budget = angular_sigma - float(theta) * beta
                pressure_budget = pressure_sigma - float(theta) * beta
                candidate_budget = max(angular_budget, pressure_budget)
                if max(angular_sigma, pressure_sigma) <= EPS:
                    route_status = "SOURCE_BUDGET_ROUTE_FALSIFIED_UNDER_CURRENT_DIAGNOSTICS"
                elif candidate_budget > threshold:
                    route_status = "CANDIDATE_DECAY_EXCEEDS_HALF_PROOF_INDEPENDENCE_REQUIRED"
                else:
                    route_status = "POSITIVE_BUT_SUBHALF_DECAY_DIAGNOSTIC"
                out.append(
                    SourceDecaySearchRow(
                        step=step,
                        time=float(time),
                        K=int(row["K"]),
                        theta=float(theta),
                        residue_key=residue_key,
                        Rplus=_fmt(rplus),
                        rho_K=_fmt(rho),
                        rho_pass=1 if rho is not None and rho < rho_threshold else 0,
                        angular_coherence=_fmt(float(row.get("AngularCoherence_K", 0.0))),
                        angular_sigma_fit=_fmt(angular_sigma),
                        angular_candidate_budget=_fmt(angular_budget),
                        pressure_survival=_fmt(max(0.0, 1.0 - float(row["PressureDecorrelationScore_K"]))),
                        pressure_sigma_fit=_fmt(pressure_sigma),
                        pressure_candidate_budget=_fmt(pressure_budget),
                        beta_fit=_fmt(beta),
                        candidate_budget=_fmt(candidate_budget),
                        bt_eta_status="eta_unavailable_no_BT_lane_observable",
                        independent_of_Rplus=0,
                        independent_of_Q=0,
                        used_in_budget=0,
                        double_count_warning=(
                            "candidate exponents are diagnostic only; no budget credit "
                            "without a proof-independent observable and no BT eta without lane labels"
                        ),
                        route_status=route_status,
                        promotion_status="NO_PROMOTION_SOURCE_DECAY_SEARCH",
                        note=(
                            "rho is an adjacent-shell proxy, not particle lineage; angular and pressure "
                            "exponents are raw diagnostics and are not credited to the Clay budget here"
                        ),
                    )
                )

    status_counts: dict[str, int] = {}
    for row in out:
        status_counts[row.route_status] = status_counts.get(row.route_status, 0) + 1
    angular_sigmas = [float(row.angular_sigma_fit) for row in out if row.angular_sigma_fit]
    pressure_sigmas = [float(row.pressure_sigma_fit) for row in out if row.pressure_sigma_fit]
    candidate_budgets = [float(row.candidate_budget) for row in out if row.candidate_budget]
    rhos = [float(row.rho_K) for row in out if row.rho_K]
    source_budget_route_falsified = bool(
        out
        and max(angular_sigmas or [0.0]) <= EPS
        and max(pressure_sigmas or [0.0]) <= EPS
    )
    summary = {
        "source_decay_search_available": True,
        "source_decay_residue_key": residue_key,
        "source_decay_theta_grid": theta_values,
        "source_decay_row_count": len(out),
        "rho_threshold": rho_threshold,
        "rho_rows": len(rhos),
        "rho_pass_rows": sum(row.rho_pass for row in out),
        "rho_sup": max(rhos) if rhos else None,
        "angular_sigma_fit_min": min(angular_sigmas) if angular_sigmas else None,
        "angular_sigma_fit_max": max(angular_sigmas) if angular_sigmas else None,
        "pressure_sigma_fit_min": min(pressure_sigmas) if pressure_sigmas else None,
        "pressure_sigma_fit_max": max(pressure_sigmas) if pressure_sigmas else None,
        "candidate_budget_inf": min(candidate_budgets) if candidate_budgets else None,
        "candidate_budget_sup": max(candidate_budgets) if candidate_budgets else None,
        "source_decay_route_status_counts": status_counts,
        "bt_lane_decay_status": "eta_unavailable_no_BT_lane_observable",
        "source_budget_route_falsified_under_current_diagnostics": source_budget_route_falsified,
        "source_decay_search_promotes": False,
        "source_decay_boundary": (
            "Sprint 46 searches for independent source-decay observables. Raw angular, "
            "pressure, and rho diagnostics do not receive budget credit without proof "
            "independence; BT eta is unavailable without lane labels."
        ),
        "source_decay_field_contract": list(SourceDecaySearchRow.__dataclass_fields__.keys()),
    }
    return out, summary


def _write_source_decay_search_csv(path: Path, rows: Iterable[SourceDecaySearchRow]) -> None:
    rows = list(rows)
    path.parent.mkdir(parents=True, exist_ok=True)
    with open(path, "w", newline="", encoding="utf-8") as handle:
        writer = csv.DictWriter(handle, fieldnames=list(SourceDecaySearchRow.__dataclass_fields__.keys()))
        writer.writeheader()
        for row in rows:
            writer.writerow(row.__dict__)


def _packet_lineage_audit_rows(
    preliminary: list[dict[str, Any]],
    meta: dict[str, Any],
    args: argparse.Namespace,
) -> tuple[list[PacketTransitionRow], list[PacketTransitionSummaryRow], dict[str, Any]]:
    if not bool(args.packet_lineage_audit or args.replenishment_decomposition_audit):
        return [], [], {
            "packet_lineage_audit_available": False,
            "packet_lineage_promotes": False,
        }
    if not preliminary:
        return [], [], {
            "packet_lineage_audit_available": False,
            "packet_lineage_promotes": False,
            "packet_lineage_unavailable_reason": "no 3d packet preliminary rows available",
        }

    threshold = 1.0 / math.sqrt(2.0)
    by_time: dict[float, list[dict[str, Any]]] = {}
    for row in preliminary:
        by_time.setdefault(float(row["t"]), []).append(row)
    times = sorted(by_time)
    dt_values = [b - a for a, b in zip(times, times[1:]) if b > a]
    default_dt = min(dt_values) if dt_values else float(meta.get("dt", 1.0))

    table_rows: list[PacketTransitionRow] = []
    summary_rows: list[PacketTransitionSummaryRow] = []
    weighted_prefix = 0.0

    for time in times:
        rows_for_time = sorted(by_time[time], key=lambda r: int(r["K"]))
        by_k = {int(row["K"]): row for row in rows_for_time}
        step = int(round(float(time) / max(default_dt, EPS)))
        for k in sorted(by_k):
            parent_row = by_k.get(k)
            child_row = by_k.get(k + 1)
            if parent_row is None or child_row is None:
                continue
            parents = list(parent_row.get("packet_summaries", []))
            children = list(child_row.get("packet_summaries", []))
            if not parents and not children:
                continue

            parents_by_lane = {int(packet["lane_int"]): packet for packet in parents}
            total_parent_mass = float(sum(float(p["mass"]) for p in parents))
            total_child_mass = float(sum(float(p["mass"]) for p in children))
            parent_mass_by_state = {
                "plus": float(sum(float(p["mass"]) for p in parents if str(p["state"]) == "plus")),
                "zero": float(sum(float(p["mass"]) for p in parents if str(p["state"]) == "zero")),
                "minus": float(sum(float(p["mass"]) for p in parents if str(p["state"]) == "minus")),
            }
            rplus = parent_mass_by_state["plus"] / (total_parent_mass + EPS)
            rzero = parent_mass_by_state["zero"] / (total_parent_mass + EPS)
            rminus = parent_mass_by_state["minus"] / (total_parent_mass + EPS)

            plus_child_total = float(sum(float(c["mass"]) for c in children if str(c["state"]) == "plus"))
            plus_from = {"plus": 0.0, "zero": 0.0, "minus": 0.0, "source": 0.0}

            for child in children:
                lane = int(child["lane_int"])
                parent = parents_by_lane.get(lane)
                child_state = str(child["state"])
                parent_state = str(parent["state"]) if parent is not None else "source"
                child_mass = float(child["mass"])
                if child_state == "plus":
                    if parent is None:
                        plus_from["source"] = plus_from.get("source", 0.0) + child_mass
                    else:
                        parent_mass = float(parent["mass"])
                        transition_mass = min(child_mass, parent_mass)
                        plus_from[parent_state] = plus_from.get(parent_state, 0.0) + transition_mass
                        excess = max(0.0, child_mass - transition_mass)
                        plus_from["source"] = plus_from.get("source", 0.0) + excess

                parent_id = "" if parent is None else str(parent["packet_id"])
                centroid_distance = None
                angle = None
                overlap_score = None
                if parent is not None:
                    parent_centroid = np.asarray(parent["centroid"], dtype=np.float64)
                    child_centroid = np.asarray(child["centroid"], dtype=np.float64)
                    centroid_distance = float(np.linalg.norm(child_centroid - parent_centroid))
                    angle = _direction_angle(
                        np.asarray(parent["direction"], dtype=np.float64),
                        np.asarray(child["direction"], dtype=np.float64),
                    )
                    overlap_score = 1.0 / (1.0 + centroid_distance)

                if parent is None:
                    status = "UNMATCHED_CHILD_COUNTS_AS_NEW_SOURCE"
                elif child_state == "plus" and parent_state == "plus":
                    status = "PLUS_TO_PLUS"
                elif child_state == "plus":
                    status = f"{parent_state.upper()}_TO_PLUS_REPLENISHMENT"
                else:
                    status = "NONPLUS_CHILD_TRANSITION"

                table_rows.append(
                    PacketTransitionRow(
                        step=step,
                        time=float(time),
                        K=int(k),
                        packet_id=str(child["packet_id"]),
                        parent_packet_id=parent_id,
                        state_K=parent_state,
                        state_Kplus1=child_state,
                        mass_K=_fmt(float(parent["mass"]) if parent is not None else None),
                        mass_Kplus1=_fmt(child_mass),
                        overlap_score=_fmt(overlap_score),
                        centroid_distance=_fmt(centroid_distance),
                        direction_angle=_fmt(angle),
                        BT_lane_id=str(child["BT_lane_id"]),
                        braid_word_id_proxy=str(child["braid_word_id_proxy"]),
                        transition_status=status,
                        note=(
                            "coarse same-snapshot K-to-K+1 packet proxy; no advected parent, "
                            "true BT lane, or braid word is certified"
                        ),
                    )
                )

            mpp = plus_from["plus"] / (parent_mass_by_state["plus"] + EPS)
            mpz = plus_from["zero"] / (parent_mass_by_state["zero"] + EPS)
            mpm = plus_from["minus"] / (parent_mass_by_state["minus"] + EPS)
            new_source = plus_from["source"] / (total_parent_mass + EPS)
            s_eff = mpz * rzero + mpm * rminus + new_source
            weighted = float((2.0 ** (0.5 * k)) * s_eff)
            weighted_prefix += weighted
            rho_packet = plus_child_total / (parent_mass_by_state["plus"] + EPS)
            pass_persistence = mpp < threshold
            pass_source_prefix = math.isfinite(weighted_prefix)
            if not parents or not children:
                route_status = "PACKET_MATCHING_RESOLUTION_INSUFFICIENT"
            elif not pass_persistence:
                route_status = "PACKET_RED_PERSISTS_OBSERVED_PREFIX"
            elif s_eff > EPS:
                route_status = "PERSISTENCE_PASSES_REPLENISHMENT_OPEN"
            else:
                route_status = "PERSISTENCE_PREFIX_PASS_SOURCE_PREFIX_EMPTY_DIAGNOSTIC_ONLY"

            summary_rows.append(
                PacketTransitionSummaryRow(
                    step=step,
                    time=float(time),
                    K=int(k),
                    packet_count_K=len(parents),
                    packet_count_Kplus1=len(children),
                    Rplus_K=_fmt(rplus),
                    Rzero_K=_fmt(rzero),
                    Rminus_K=_fmt(rminus),
                    M_plus_plus=_fmt(mpp),
                    M_plus_zero=_fmt(mpz),
                    M_plus_minus=_fmt(mpm),
                    s_eff_K=_fmt(s_eff),
                    weighted_s_eff_K=_fmt(weighted),
                    rho_packet_K=_fmt(rho_packet),
                    pass_persistence=1 if pass_persistence else 0,
                    pass_source_prefix=1 if pass_source_prefix else 0,
                    route_status=route_status,
                    promotion_status="NO_PROMOTION_PACKET_LINEAGE_DIAGNOSTIC",
                    note=(
                        "M entries are coarse packet lineage proxies. Closure requires true parent "
                        "confidence, uniform persistence below 1/sqrt(2), and weighted source summability."
                    ),
                )
            )

    status_counts: dict[str, int] = {}
    for row in summary_rows:
        status_counts[row.route_status] = status_counts.get(row.route_status, 0) + 1
    mpps = [float(row.M_plus_plus) for row in summary_rows if row.M_plus_plus]
    weighted_values = [float(row.weighted_s_eff_K) for row in summary_rows if row.weighted_s_eff_K]
    parent_rows = sum(1 for row in table_rows if row.parent_packet_id)
    unmatched_rows = len(table_rows) - parent_rows
    all_persistence = bool(summary_rows and all(row.pass_persistence for row in summary_rows))
    source_prefix_finite = bool(summary_rows and all(math.isfinite(v) for v in weighted_values))
    falsifies = bool(summary_rows and any(row.route_status == "PACKET_RED_PERSISTS_OBSERVED_PREFIX" for row in summary_rows))
    summary = {
        "packet_lineage_audit_available": True,
        "packet_lineage_residue_key": str(args.residue_key),
        "packet_grid": int(args.packet_grid),
        "packet_active_quantile": float(args.packet_active_quantile),
        "packet_state_threshold": float(args.packet_state_threshold),
        "packet_lineage_row_count": len(table_rows),
        "packet_transition_summary_row_count": len(summary_rows),
        "packet_parent_rows": parent_rows,
        "packet_unmatched_rows": unmatched_rows,
        "packet_confident_parent_rows": parent_rows,
        "persistence_threshold": threshold,
        "m_plus_plus_sup": max(mpps) if mpps else None,
        "m_plus_plus_pass_rows": sum(row.pass_persistence for row in summary_rows),
        "s_eff_weighted_prefix_sum": float(sum(weighted_values)) if weighted_values else None,
        "source_summability_prefix_finite": source_prefix_finite,
        "packet_route_status_counts": status_counts,
        "bt_lane_status": "eta_unavailable_no_true_BT_lane_labels",
        "packet_lineage_closes_source_budget_under_current_diagnostics": False,
        "packet_lineage_falsifies_source_budget_under_current_diagnostics": falsifies,
        "packet_lineage_promotes": False,
        "packet_lineage_boundary": (
            "Sprint 47A uses coarse spatial packets as an observed-prefix lineage proxy. "
            "It does not certify advected material parents, true BT lanes, braid words, "
            "uniform source summability, stretch absorption, no finite-time blowup, or Clay regularity."
        ),
        "packet_lineage_all_persistence_prefix_pass": all_persistence,
        "packet_lineage_field_contract": list(PacketTransitionRow.__dataclass_fields__.keys()),
        "packet_lineage_summary_field_contract": list(PacketTransitionSummaryRow.__dataclass_fields__.keys()),
    }
    return table_rows, summary_rows, summary


def _write_packet_transition_csv(path: Path, rows: Iterable[PacketTransitionRow]) -> None:
    rows = list(rows)
    path.parent.mkdir(parents=True, exist_ok=True)
    with open(path, "w", newline="", encoding="utf-8") as handle:
        writer = csv.DictWriter(handle, fieldnames=list(PacketTransitionRow.__dataclass_fields__.keys()))
        writer.writeheader()
        for row in rows:
            writer.writerow(row.__dict__)


def _write_packet_transition_summary_csv(path: Path, rows: Iterable[PacketTransitionSummaryRow]) -> None:
    rows = list(rows)
    path.parent.mkdir(parents=True, exist_ok=True)
    with open(path, "w", newline="", encoding="utf-8") as handle:
        writer = csv.DictWriter(handle, fieldnames=list(PacketTransitionSummaryRow.__dataclass_fields__.keys()))
        writer.writeheader()
        for row in rows:
            writer.writerow(row.__dict__)


def _read_packet_transition_summary_csv(path: Path) -> list[PacketTransitionSummaryRow]:
    if not path.exists():
        raise SystemExit(f"--replay-packet-summary path does not exist: {path}")
    rows: list[PacketTransitionSummaryRow] = []
    with open(path, newline="", encoding="utf-8") as handle:
        reader = csv.DictReader(handle)
        required = set(PacketTransitionSummaryRow.__dataclass_fields__.keys())
        missing = sorted(required.difference(reader.fieldnames or []))
        if missing:
            raise SystemExit(f"{path} is missing packet summary columns: {', '.join(missing)}")
        for raw in reader:
            rows.append(
                PacketTransitionSummaryRow(
                    step=int(raw["step"]),
                    time=float(raw["time"]),
                    K=int(raw["K"]),
                    packet_count_K=int(raw["packet_count_K"]),
                    packet_count_Kplus1=int(raw["packet_count_Kplus1"]),
                    Rplus_K=str(raw["Rplus_K"]),
                    Rzero_K=str(raw["Rzero_K"]),
                    Rminus_K=str(raw["Rminus_K"]),
                    M_plus_plus=str(raw["M_plus_plus"]),
                    M_plus_zero=str(raw["M_plus_zero"]),
                    M_plus_minus=str(raw["M_plus_minus"]),
                    s_eff_K=str(raw["s_eff_K"]),
                    weighted_s_eff_K=str(raw["weighted_s_eff_K"]),
                    rho_packet_K=str(raw["rho_packet_K"]),
                    pass_persistence=int(raw["pass_persistence"]),
                    pass_source_prefix=int(raw["pass_source_prefix"]),
                    route_status=str(raw["route_status"]),
                    promotion_status=str(raw["promotion_status"]),
                    note=str(raw["note"]),
                )
            )
    return rows


def _numeric_cell(value: str | float | int | None, default: float = 0.0) -> float:
    if value is None:
        return default
    try:
        out = float(value)
    except (TypeError, ValueError):
        return default
    return out if math.isfinite(out) else default


def _read_material_parent_summary_csv(path: Path) -> list[MaterialParentSummaryRow]:
    if not path.exists():
        raise SystemExit(f"--replay-material-parent-summary path does not exist: {path}")
    rows: list[MaterialParentSummaryRow] = []
    with open(path, newline="", encoding="utf-8") as handle:
        reader = csv.DictReader(handle)
        required = set(MaterialParentSummaryRow.__dataclass_fields__.keys())
        missing = sorted(required.difference(reader.fieldnames or []))
        if missing:
            raise SystemExit(f"{path} is missing material parent summary columns: {', '.join(missing)}")
        for raw in reader:
            rows.append(
                MaterialParentSummaryRow(
                    time=float(raw["time"]),
                    K_child=int(raw["K_child"]),
                    M_plus_plus_material=str(raw["M_plus_plus_material"]),
                    source_true_new=str(raw["source_true_new"]),
                    source_tracking_uncertain=str(raw["source_tracking_uncertain"]),
                    source_cross_shell=str(raw["source_cross_shell"]),
                    source_low_shell_injection=str(raw["source_low_shell_injection"]),
                    source_total_material=str(raw["source_total_material"]),
                    weighted_true_new=str(raw["weighted_true_new"]),
                    weighted_tracking_uncertain=str(raw["weighted_tracking_uncertain"]),
                    weighted_cross_shell=str(raw["weighted_cross_shell"]),
                    weighted_low_shell_injection=str(raw["weighted_low_shell_injection"]),
                    weighted_total_material=str(raw["weighted_total_material"]),
                    sigma_true_new_fit=str(raw["sigma_true_new_fit"]),
                    sigma_tracking_uncertain_fit=str(raw["sigma_tracking_uncertain_fit"]),
                    sigma_cross_shell_fit=str(raw["sigma_cross_shell_fit"]),
                    sigma_low_shell_fit=str(raw["sigma_low_shell_fit"]),
                    sigma_total_material_fit=str(raw["sigma_total_material_fit"]),
                    route_status=str(raw["route_status"]),
                )
            )
    return rows


def _write_material_parent_summary_csv(path: Path, rows: Iterable[MaterialParentSummaryRow]) -> None:
    rows = list(rows)
    path.parent.mkdir(parents=True, exist_ok=True)
    with open(path, "w", newline="", encoding="utf-8") as handle:
        writer = csv.DictWriter(handle, fieldnames=list(MaterialParentSummaryRow.__dataclass_fields__.keys()))
        writer.writeheader()
        for row in rows:
            writer.writerow(row.__dict__)


def _material_parent_route_status(
    sigma_true_new: float,
    sigma_tracking_uncertain: float,
    sigma_cross_shell: float,
    sigma_low_shell: float,
    weighted_true_new: float,
    weighted_tracking_uncertain: float,
    weighted_cross_shell: float,
    weighted_low_shell: float,
) -> str:
    weighted_components = {
        "true_new": weighted_true_new,
        "tracking_uncertain": weighted_tracking_uncertain,
        "cross_shell": weighted_cross_shell,
        "low_shell": weighted_low_shell,
    }
    dominant = max(weighted_components, key=weighted_components.get)
    if dominant == "tracking_uncertain" and weighted_tracking_uncertain > weighted_true_new:
        return "TRACKING_UNCERTAIN_NEEDS_DENSER_SNAPSHOTS"
    if dominant in {"cross_shell", "low_shell"} and weighted_components[dominant] > weighted_true_new:
        return "ADJACENT_PACKET_THEOREM_INSUFFICIENT"
    if sigma_true_new <= 0.5:
        return "TRUE_NEW_SOURCE_SUBCRITICAL"
    if sigma_true_new > 0.5 and weighted_tracking_uncertain <= weighted_true_new:
        return "MATERIAL_PARENT_REPAIRS_NEW_SOURCE_DIAGNOSTIC_ONLY"
    return "TRACKING_UNCERTAIN_NEEDS_DENSER_SNAPSHOTS"


def _material_parent_replay_summary(rows: list[MaterialParentSummaryRow], args: argparse.Namespace) -> dict[str, Any]:
    if not rows:
        return {
            "material_parent_replay_available": False,
            "material_parent_replay_promotes": False,
            "material_parent_replay_unavailable_reason": "material parent summary rows are required",
        }

    by_time: dict[float, list[MaterialParentSummaryRow]] = {}
    for row in rows:
        by_time.setdefault(float(row.time), []).append(row)

    def values(field: str) -> list[float]:
        return [_numeric_cell(getattr(row, field)) for row in rows]

    def sigma_values(field: str) -> list[float]:
        return [_numeric_cell(getattr(row, field)) for row in rows if str(getattr(row, field)) != ""]

    sigma_true = sigma_values("sigma_true_new_fit")
    sigma_tracking = sigma_values("sigma_tracking_uncertain_fit")
    sigma_cross = sigma_values("sigma_cross_shell_fit")
    sigma_low = sigma_values("sigma_low_shell_fit")
    sigma_total = sigma_values("sigma_total_material_fit")
    weighted_true = values("weighted_true_new")
    weighted_tracking = values("weighted_tracking_uncertain")
    weighted_cross = values("weighted_cross_shell")
    weighted_low = values("weighted_low_shell_injection")
    weighted_total = values("weighted_total_material")

    sigma_true_new = min(sigma_true) if sigma_true else 0.0
    sigma_tracking_uncertain = max(sigma_tracking) if sigma_tracking else 0.0
    sigma_cross_shell = max(sigma_cross) if sigma_cross else 0.0
    sigma_low_shell = max(sigma_low) if sigma_low else 0.0
    sigma_total_material = min(sigma_total) if sigma_total else 0.0

    route_status = _material_parent_route_status(
        sigma_true_new=sigma_true_new,
        sigma_tracking_uncertain=sigma_tracking_uncertain,
        sigma_cross_shell=sigma_cross_shell,
        sigma_low_shell=sigma_low_shell,
        weighted_true_new=float(sum(weighted_true)),
        weighted_tracking_uncertain=float(sum(weighted_tracking)),
        weighted_cross_shell=float(sum(weighted_cross)),
        weighted_low_shell=float(sum(weighted_low)),
    )
    input_status_counts: dict[str, int] = {}
    for row in rows:
        input_status_counts[row.route_status] = input_status_counts.get(row.route_status, 0) + 1

    return {
        "material_parent_replay_available": True,
        "diagnostic_mode": "sprint49_material_parent_replay_from_gpu_summary",
        "material_parent_summary_input": str(args.replay_material_parent_summary),
        "material_parent_summary_row_count": len(rows),
        "material_parent_time_count": len(by_time),
        "material_parent_K_child_count": len({int(row.K_child) for row in rows}),
        "sigma_true_new": sigma_true_new,
        "sigma_tracking_uncertain": sigma_tracking_uncertain,
        "sigma_cross_shell": sigma_cross_shell,
        "sigma_low_shell": sigma_low_shell,
        "sigma_total_material": sigma_total_material,
        "sigma_true_new_fit_min": min(sigma_true) if sigma_true else None,
        "sigma_true_new_fit_max": max(sigma_true) if sigma_true else None,
        "sigma_tracking_uncertain_fit_min": min(sigma_tracking) if sigma_tracking else None,
        "sigma_tracking_uncertain_fit_max": max(sigma_tracking) if sigma_tracking else None,
        "sigma_cross_shell_fit_min": min(sigma_cross) if sigma_cross else None,
        "sigma_cross_shell_fit_max": max(sigma_cross) if sigma_cross else None,
        "sigma_low_shell_fit_min": min(sigma_low) if sigma_low else None,
        "sigma_low_shell_fit_max": max(sigma_low) if sigma_low else None,
        "sigma_total_material_fit_min": min(sigma_total) if sigma_total else None,
        "sigma_total_material_fit_max": max(sigma_total) if sigma_total else None,
        "weighted_true_new_prefix_sum": float(sum(weighted_true)),
        "weighted_tracking_uncertain_prefix_sum": float(sum(weighted_tracking)),
        "weighted_cross_shell_prefix_sum": float(sum(weighted_cross)),
        "weighted_low_shell_injection_prefix_sum": float(sum(weighted_low)),
        "weighted_total_material_prefix_sum": float(sum(weighted_total)),
        "material_parent_route_status": route_status,
        "material_parent_input_route_status_counts": input_status_counts,
        "material_parent_replay_uses_gpu_parent_artifacts": True,
        "material_parent_replay_reruns_shell_packets": False,
        "material_parent_replay_promotes": False,
        "clay_promotion": False,
        "navier_stokes_promotion": False,
        "promotion_status": "NO_PROMOTION_MATERIAL_PARENT_REPLAY_DIAGNOSTIC",
        "receipt_alignment": "DASHI.Physics.Closure.ClaySprintFortyNineMaterialParentReplayReceipt",
        "evidence_boundary": (
            "Sprint 49 replay consumes GPU-produced material parent summaries only. "
            "It does not recompute N64 packet diagnostics on CPU and does not prove "
            "source summability, the physical bridge, stretch absorption, no finite-time blowup, "
            "or Clay regularity."
        ),
        "material_parent_summary_field_contract": list(MaterialParentSummaryRow.__dataclass_fields__.keys()),
    }


def _replenishment_decomposition_rows(
    packet_summary_rows: list[PacketTransitionSummaryRow],
    args: argparse.Namespace,
) -> tuple[list[ReplenishmentDecompositionRow], dict[str, Any]]:
    if not bool(args.replenishment_decomposition_audit):
        return [], {
            "replenishment_decomposition_available": False,
            "replenishment_decomposition_promotes": False,
        }
    if not packet_summary_rows:
        return [], {
            "replenishment_decomposition_available": False,
            "replenishment_decomposition_promotes": False,
            "replenishment_decomposition_unavailable_reason": "packet lineage summary rows are required",
        }

    threshold = float(args.budget_threshold)
    persistence_threshold = 1.0 / math.sqrt(2.0)
    derived: list[dict[str, Any]] = []
    for row in packet_summary_rows:
        k = int(row.K)
        weight = float(2.0 ** (0.5 * k))
        rplus = _numeric_cell(row.Rplus_K)
        rzero = _numeric_cell(row.Rzero_K)
        rminus = _numeric_cell(row.Rminus_K)
        mpp = _numeric_cell(row.M_plus_plus)
        mpz = _numeric_cell(row.M_plus_zero)
        mpm = _numeric_cell(row.M_plus_minus)
        source_plus = max(0.0, mpp * rplus)
        source_zero = max(0.0, mpz * rzero)
        source_minus = max(0.0, mpm * rminus)
        source_total = max(0.0, _numeric_cell(row.s_eff_K))
        source_new = max(0.0, source_total - source_zero - source_minus)
        derived.append(
            {
                "row": row,
                "K": k,
                "time": float(row.time),
                "Rplus_K": rplus,
                "Rzero_K": rzero,
                "Rminus_K": rminus,
                "M_plus_plus": mpp,
                "M_plus_zero": mpz,
                "M_plus_minus": mpm,
                "source_from_plus": source_plus,
                "source_from_zero": source_zero,
                "source_from_minus": source_minus,
                "source_new_unmatched": source_new,
                "source_total_eff": source_total,
                "weighted_plus_source": weight * source_plus,
                "weighted_zero_source": weight * source_zero,
                "weighted_minus_source": weight * source_minus,
                "weighted_new_source": weight * source_new,
                "weighted_total_source": weight * source_total,
            }
        )

    by_time: dict[float, list[dict[str, Any]]] = {}
    for item in derived:
        by_time.setdefault(float(item["time"]), []).append(item)
    slopes_by_time: dict[float, dict[str, float]] = {}
    for time, items in by_time.items():
        xs = [float(item["K"]) for item in items]
        slopes_by_time[time] = {
            "zero": max(0.0, -_finite_slope(xs, [float(item["source_from_zero"]) + EPS for item in items])),
            "minus": max(0.0, -_finite_slope(xs, [float(item["source_from_minus"]) + EPS for item in items])),
            "new": max(0.0, -_finite_slope(xs, [float(item["source_new_unmatched"]) + EPS for item in items])),
            "total": max(0.0, -_finite_slope(xs, [float(item["source_total_eff"]) + EPS for item in items])),
        }

    out: list[ReplenishmentDecompositionRow] = []
    for item in derived:
        row = item["row"]
        slopes = slopes_by_time[float(item["time"])]
        pass_persistence = 1 if float(item["M_plus_plus"]) < persistence_threshold else 0
        pass_zero = 1 if slopes["zero"] > threshold else 0
        pass_minus = 1 if slopes["minus"] > threshold else 0
        pass_new = 1 if slopes["new"] > threshold else 0
        pass_total = 1 if slopes["total"] > threshold else 0
        if not pass_persistence:
            route_status = "PERSISTENCE_FAILS_BEFORE_REPLENISHMENT"
        elif float(item["source_total_eff"]) <= EPS:
            route_status = "REPLENISHMENT_EMPTY_OBSERVED_PREFIX"
        elif pass_zero and pass_minus and pass_new and pass_total:
            route_status = "REPLENISHMENT_EXPONENTS_PASS_DIAGNOSTIC_ONLY"
        else:
            route_status = "REPLENISHMENT_SOURCE_SUBHALF_OR_GROWING"
        out.append(
            ReplenishmentDecompositionRow(
                step=int(row.step),
                time=float(row.time),
                K=int(row.K),
                Rminus_K=_fmt(float(item["Rminus_K"])),
                Rzero_K=_fmt(float(item["Rzero_K"])),
                Rplus_K=_fmt(float(item["Rplus_K"])),
                M_plus_plus=_fmt(float(item["M_plus_plus"])),
                M_plus_zero=_fmt(float(item["M_plus_zero"])),
                M_plus_minus=_fmt(float(item["M_plus_minus"])),
                source_from_plus=_fmt(float(item["source_from_plus"])),
                source_from_zero=_fmt(float(item["source_from_zero"])),
                source_from_minus=_fmt(float(item["source_from_minus"])),
                source_new_unmatched=_fmt(float(item["source_new_unmatched"])),
                source_total_eff=_fmt(float(item["source_total_eff"])),
                weighted_plus_source=_fmt(float(item["weighted_plus_source"])),
                weighted_zero_source=_fmt(float(item["weighted_zero_source"])),
                weighted_minus_source=_fmt(float(item["weighted_minus_source"])),
                weighted_new_source=_fmt(float(item["weighted_new_source"])),
                weighted_total_source=_fmt(float(item["weighted_total_source"])),
                sigma_zero_fit=_fmt(slopes["zero"]),
                sigma_minus_fit=_fmt(slopes["minus"]),
                sigma_new_fit=_fmt(slopes["new"]),
                sigma_total_fit=_fmt(slopes["total"]),
                pass_persistence=pass_persistence,
                pass_zero_source=pass_zero,
                pass_minus_source=pass_minus,
                pass_new_source=pass_new,
                pass_total_source=pass_total,
                route_status=route_status,
                promotion_status="NO_PROMOTION_REPLENISHMENT_DIAGNOSTIC",
                note=(
                    "Sprint 48 decomposition uses Sprint 47 coarse packet summaries. "
                    "It does not certify material parents or source summability."
                ),
            )
        )

    status_counts: dict[str, int] = {}
    for row in out:
        status_counts[row.route_status] = status_counts.get(row.route_status, 0) + 1
    sigma_zero = [float(row.sigma_zero_fit) for row in out if row.sigma_zero_fit]
    sigma_minus = [float(row.sigma_minus_fit) for row in out if row.sigma_minus_fit]
    sigma_new = [float(row.sigma_new_fit) for row in out if row.sigma_new_fit]
    sigma_total = [float(row.sigma_total_fit) for row in out if row.sigma_total_fit]
    weighted_plus = [float(row.weighted_plus_source) for row in out if row.weighted_plus_source]
    weighted_zero = [float(row.weighted_zero_source) for row in out if row.weighted_zero_source]
    weighted_minus = [float(row.weighted_minus_source) for row in out if row.weighted_minus_source]
    weighted_new = [float(row.weighted_new_source) for row in out if row.weighted_new_source]
    weighted_total = [float(row.weighted_total_source) for row in out if row.weighted_total_source]
    summary = {
        "replenishment_decomposition_available": True,
        "replenishment_residue_key": str(args.residue_key),
        "replenishment_threshold": threshold,
        "replenishment_decomposition_row_count": len(out),
        "replenishment_route_status_counts": status_counts,
        "replenishment_pass_persistence_rows": sum(row.pass_persistence for row in out),
        "replenishment_pass_zero_source_rows": sum(row.pass_zero_source for row in out),
        "replenishment_pass_minus_source_rows": sum(row.pass_minus_source for row in out),
        "replenishment_pass_new_source_rows": sum(row.pass_new_source for row in out),
        "replenishment_pass_total_source_rows": sum(row.pass_total_source for row in out),
        "sigma_zero_fit_min": min(sigma_zero) if sigma_zero else None,
        "sigma_zero_fit_max": max(sigma_zero) if sigma_zero else None,
        "sigma_minus_fit_min": min(sigma_minus) if sigma_minus else None,
        "sigma_minus_fit_max": max(sigma_minus) if sigma_minus else None,
        "sigma_new_fit_min": min(sigma_new) if sigma_new else None,
        "sigma_new_fit_max": max(sigma_new) if sigma_new else None,
        "sigma_total_fit_min": min(sigma_total) if sigma_total else None,
        "sigma_total_fit_max": max(sigma_total) if sigma_total else None,
        "weighted_plus_source_prefix_sum": float(sum(weighted_plus)) if weighted_plus else None,
        "weighted_zero_source_prefix_sum": float(sum(weighted_zero)) if weighted_zero else None,
        "weighted_minus_source_prefix_sum": float(sum(weighted_minus)) if weighted_minus else None,
        "weighted_new_source_prefix_sum": float(sum(weighted_new)) if weighted_new else None,
        "weighted_total_source_prefix_sum": float(sum(weighted_total)) if weighted_total else None,
        "total_positive_source_summability_observed_prefix": False,
        "packet_transition_closes_red_tail_under_current_diagnostics": False,
        "replenishment_decomposition_promotes": False,
        "replenishment_decomposition_boundary": (
            "Sprint 48 decomposes observed-prefix replenishment from coarse packet rows. "
            "It does not prove material packet lineage, independent source decay, weighted "
            "summability, stretch absorption, no finite-time blowup, or Clay regularity."
        ),
        "replenishment_decomposition_field_contract": list(ReplenishmentDecompositionRow.__dataclass_fields__.keys()),
    }
    return out, summary


def _write_replenishment_decomposition_csv(path: Path, rows: Iterable[ReplenishmentDecompositionRow]) -> None:
    rows = list(rows)
    path.parent.mkdir(parents=True, exist_ok=True)
    with open(path, "w", newline="", encoding="utf-8") as handle:
        writer = csv.DictWriter(handle, fieldnames=list(ReplenishmentDecompositionRow.__dataclass_fields__.keys()))
        writer.writeheader()
        for row in rows:
            writer.writerow(row.__dict__)


def _checks(rows: list[HarnessRow], mode_summary: dict[str, Any]) -> dict[str, Any]:
    finite_c = [r.C_K for r in rows if math.isfinite(r.C_K)]
    finite_mpp = [r.M_plus_plus for r in rows if math.isfinite(r.M_plus_plus)]
    weighted = [r.weighted_s_eff_K for r in rows if math.isfinite(r.weighted_s_eff_K)]
    budgets = [r.budget_K for r in rows if math.isfinite(r.budget_K)]
    sup_c = max(finite_c) if finite_c else math.inf
    sup_mpp = max(finite_mpp) if finite_mpp else math.inf
    source_sum = float(sum(weighted)) if weighted else math.inf
    inf_budget = min(budgets) if budgets else -math.inf
    bridge_available = bool(mode_summary.get("physical_bridge_available", False))
    persistence_pass = bool(sup_mpp < 1.0 / math.sqrt(2.0))
    budget_pass = bool(inf_budget > 0.5)
    promotion_status = "NO_PROMOTION_DIAGNOSTIC_ONLY"
    if bridge_available and not budget_pass:
        promotion_status = "NO_PROMOTION_BUDGET_FAIL"
    checks = {
        **mode_summary,
        "sup_C_K": float(sup_c),
        "sup_M_plus_plus": float(sup_mpp),
        "weighted_source_partial_sum": source_sum,
        "inf_budget_K": float(inf_budget),
        "bridgeTest_finite_on_observed_grid": bool(math.isfinite(sup_c)) if bridge_available else False,
        "persistenceTest_observed": persistence_pass if bridge_available else False,
        "sourceSummabilityTest_finite_prefix": bool(math.isfinite(source_sum)) if bridge_available else False,
        "budgetTest_observed": budget_pass if bridge_available else False,
        "pass": bool(bridge_available and math.isfinite(sup_c) and persistence_pass and math.isfinite(source_sum) and budget_pass),
        "fail_type_1_fake_residue": bool(bridge_available and not math.isfinite(sup_c)),
        "fail_type_2_red_persists": bool(bridge_available and not persistence_pass),
        "fail_type_3_weighted_source_diverges": bool(bridge_available and not math.isfinite(source_sum)),
        "fail_type_4_budget_fails": bool(bridge_available and not budget_pass),
        "promotion_status": promotion_status,
        "clay_navier_stokes_promoted": False,
    }
    if not bridge_available:
        checks["fail_closed_reason"] = mode_summary.get("reason", "physical bridge unavailable")
    return checks


def _run_replenishment_replay(args: argparse.Namespace) -> None:
    if not bool(args.replenishment_decomposition_audit):
        args.replenishment_decomposition_audit = True
    args.out_dir.mkdir(parents=True, exist_ok=True)
    packet_summary_rows = _read_packet_transition_summary_csv(args.replay_packet_summary)
    replenishment_rows, replenishment_summary = _replenishment_decomposition_rows(packet_summary_rows, args)

    packet_summary_copy_path = args.out_dir / "ns_packet_transition_summary.csv"
    replenishment_decomposition_path = args.out_dir / "ns_replenishment_decomposition.csv"
    replenishment_summary_path = args.out_dir / "ns_replenishment_summary.json"
    checks_path = args.out_dir / "ns_diagnostic_checks.json"
    manifest_path = args.out_dir / "ns_diagnostic_manifest.json"

    _write_packet_transition_summary_csv(packet_summary_copy_path, packet_summary_rows)
    _write_replenishment_decomposition_csv(replenishment_decomposition_path, replenishment_rows)

    checks = {
        "diagnostic_mode": "sprint48_replenishment_replay_from_packet_summary",
        "source": str(args.replay_packet_summary),
        "physical_bridge_available": False,
        "packet_summary_replay": True,
        "packet_transition_summary_row_count": len(packet_summary_rows),
        "clay_navier_stokes_promoted": False,
        "promotion_status": "NO_PROMOTION_REPLENISHMENT_REPLAY_DIAGNOSTIC",
        "pass": False,
        "evidence_boundary": (
            "Replay consumes Sprint 47 packet summary rows only. It does not rerun "
            "truth loading, FFT shell projection, packet matching, physical bridge "
            "estimation, stretch absorption, no finite-time blowup, or Clay regularity."
        ),
    }
    checks.update(replenishment_summary)
    manifest = {
        "source": str(args.replay_packet_summary),
        "meta": {
            "replay_mode": "sprint48_replenishment_from_packet_transition_summary",
            "packet_summary_input": str(args.replay_packet_summary),
        },
        "row_count": 0,
        "packet_transition_summary_row_count": len(packet_summary_rows),
        "replenishment_decomposition_row_count": len(replenishment_rows),
        "outputs": {
            "packet_transition_summary_csv": str(packet_summary_copy_path),
            "replenishment_decomposition": str(replenishment_decomposition_path),
            "replenishment_summary": str(replenishment_summary_path),
            "checks": str(checks_path),
            "manifest": str(manifest_path),
        },
        "receipt_alignment": "DASHI.Physics.Closure.ClaySprintFortyEightReplenishmentDecompositionReceipt",
        "evidence_boundary": "replay diagnostic only; no Navier-Stokes theorem or Clay promotion",
    }
    checks_path.write_text(json.dumps(checks, indent=2, allow_nan=True), encoding="utf-8")
    replenishment_summary_path.write_text(json.dumps(replenishment_summary, indent=2, allow_nan=True), encoding="utf-8")
    manifest_path.write_text(json.dumps(manifest, indent=2, allow_nan=True), encoding="utf-8")
    print(
        f"[ns-harness] replay wrote {packet_summary_copy_path}, "
        f"{replenishment_decomposition_path}, {replenishment_summary_path}, "
        f"{checks_path}, {manifest_path}"
    )
    print(
        "[ns-harness] "
        f"mode={checks.get('diagnostic_mode')} pass={checks.get('pass')} "
        f"rows={checks.get('replenishment_decomposition_row_count')} "
        f"promotion={checks.get('promotion_status')}"
    )


def _run_material_parent_replay(args: argparse.Namespace) -> None:
    material_rows = _read_material_parent_summary_csv(args.replay_material_parent_summary)
    material_summary = _material_parent_replay_summary(material_rows, args)

    args.out_dir.mkdir(parents=True, exist_ok=True)
    material_summary_csv_path = args.out_dir / "ns_material_parent_summary.csv"
    material_summary_json_path = args.out_dir / "ns_material_parent_summary.json"
    checks_path = args.out_dir / "ns_diagnostic_checks.json"
    manifest_path = args.out_dir / "ns_diagnostic_manifest.json"

    _write_material_parent_summary_csv(material_summary_csv_path, material_rows)
    checks = {
        **material_summary,
        "diagnostic_backend": "gpu_artifact_replay",
        "physical_bridge_available": False,
        "source_truth_loaded": False,
        "promotion_status": "NO_PROMOTION_MATERIAL_PARENT_REPLAY_DIAGNOSTIC",
    }
    manifest = {
        "source": str(args.replay_material_parent_summary),
        "parameters": {
            "replay_mode": "sprint49_material_parent_from_gpu_summary",
            "material_parent_summary_input": str(args.replay_material_parent_summary),
            "budget_threshold": float(args.budget_threshold),
        },
        "diagnostic_mode": "sprint49_material_parent_replay_from_gpu_summary",
        "material_parent_summary_row_count": len(material_rows),
        "outputs": {
            "material_parent_summary_csv": str(material_summary_csv_path),
            "material_parent_summary": str(material_summary_json_path),
            "checks": str(checks_path),
            "manifest": str(manifest_path),
        },
        "receipt_alignment": "DASHI.Physics.Closure.ClaySprintFortyNineMaterialParentReplayReceipt",
        "evidence_boundary": material_summary.get("evidence_boundary"),
        "promotion_status": "NO_PROMOTION_MATERIAL_PARENT_REPLAY_DIAGNOSTIC",
        "clay_promotion": False,
        "navier_stokes_promotion": False,
    }
    checks_path.write_text(json.dumps(checks, indent=2, allow_nan=True), encoding="utf-8")
    material_summary_json_path.write_text(json.dumps(material_summary, indent=2, allow_nan=True), encoding="utf-8")
    manifest_path.write_text(json.dumps(manifest, indent=2, allow_nan=True), encoding="utf-8")
    print(
        f"[ns-harness] material-parent replay wrote {material_summary_csv_path}, "
        f"{material_summary_json_path}, {checks_path}, {manifest_path}"
    )
    print(
        "[ns-harness] material-parent replay summary: "
        f"rows={checks.get('material_parent_summary_row_count')} "
        f"sigma_true_new={checks.get('sigma_true_new')} "
        f"sigma_tracking_uncertain={checks.get('sigma_tracking_uncertain')} "
        f"route={checks.get('material_parent_route_status')}"
    )


def _load_ternary_cross_shell_summary(path: Path) -> dict[str, Any]:
    if not path.exists():
        raise SystemExit(f"--replay-ternary-cross-shell-summary path does not exist: {path}")
    try:
        summary = json.loads(path.read_text(encoding="utf-8"))
    except json.JSONDecodeError as exc:
        raise SystemExit(f"{path} is not valid JSON: {exc}") from exc
    if not isinstance(summary, dict):
        raise SystemExit(f"{path} must contain a JSON object")
    missing = sorted(TERNARY_CROSS_SHELL_REQUIRED_SUMMARY_FIELDS.difference(summary.keys()))
    if missing:
        raise SystemExit(f"{path} is missing ternary cross-shell summary fields: {', '.join(missing)}")
    if summary.get("contract") != "ns_ternary_cross_shell_artifact":
        raise SystemExit(f"{path} contract is not ns_ternary_cross_shell_artifact")
    return summary


def _copy_optional_sibling(src_summary: Path, out_dir: Path, filename: str) -> str | None:
    src = src_summary.parent / filename
    if not src.exists():
        return None
    dst = out_dir / filename
    shutil.copyfile(src, dst)
    return str(dst)


def _run_ternary_cross_shell_replay(args: argparse.Namespace) -> None:
    source = args.replay_ternary_cross_shell_summary
    source_summary = _load_ternary_cross_shell_summary(source)

    args.out_dir.mkdir(parents=True, exist_ok=True)
    summary_path = args.out_dir / "ns_ternary_cross_shell_summary.json"
    checks_path = args.out_dir / "ns_diagnostic_checks.json"
    manifest_path = args.out_dir / "ns_diagnostic_manifest.json"

    shutil.copyfile(source, summary_path)
    matrix_copy = _copy_optional_sibling(source, args.out_dir, "ns_full_ternary_transition_matrix.csv")
    decomposition_copy = _copy_optional_sibling(source, args.out_dir, "ns_cross_shell_source_decomposition.csv")

    checks = {
        **source_summary,
        "ternary_cross_shell_replay_available": True,
        "diagnostic_mode": "sprint50_ternary_cross_shell_replay_from_gpu_summary",
        "ternary_cross_shell_summary_input": str(source),
        "diagnostic_backend": "gpu_artifact_replay",
        "physical_bridge_available": False,
        "source_truth_loaded": False,
        "material_parent_lineage_recomputed": False,
        "ternary_cross_shell_replay_promotes": False,
        "clay_promotion": False,
        "navier_stokes_promotion": False,
        "clay_navier_stokes_promoted": False,
        "pass": False,
        "promotion_status": "NO_PROMOTION_TERNARY_CROSS_SHELL_REPLAY_DIAGNOSTIC",
        "receipt_alignment": "DASHI.Physics.Closure.ClaySprintFiftyFullTernaryCrossShellAuditReceipt",
        "evidence_boundary": (
            "Sprint 50 replay consumes dashiCFD ternary cross-shell summaries only. "
            "It does not recompute material-parent lineage, prove cross-shell summability, "
            "upgrade the BT-distance proxy to a theorem-grade metric, prove the physical "
            "bridge, prove stretch absorption, prove no finite-time blowup, or promote Clay regularity."
        ),
        "ternary_cross_shell_summary_field_contract": sorted(TERNARY_CROSS_SHELL_REQUIRED_SUMMARY_FIELDS),
    }
    manifest = {
        "source": str(source),
        "parameters": {
            "replay_mode": "sprint50_ternary_cross_shell_from_gpu_summary",
            "ternary_cross_shell_summary_input": str(source),
        },
        "diagnostic_mode": "sprint50_ternary_cross_shell_replay_from_gpu_summary",
        "ternary_cross_shell_matrix_entry_count": source_summary.get("matrix_entry_count"),
        "ternary_cross_shell_decomposition_entry_count": source_summary.get("source_decomposition_entry_count"),
        "outputs": {
            "ternary_cross_shell_summary": str(summary_path),
            "full_ternary_transition_matrix_csv": matrix_copy,
            "cross_shell_source_decomposition_csv": decomposition_copy,
            "checks": str(checks_path),
            "manifest": str(manifest_path),
        },
        "receipt_alignment": "DASHI.Physics.Closure.ClaySprintFiftyFullTernaryCrossShellAuditReceipt",
        "evidence_boundary": checks["evidence_boundary"],
        "promotion_status": checks["promotion_status"],
        "clay_promotion": False,
        "navier_stokes_promotion": False,
    }
    checks_path.write_text(json.dumps(checks, indent=2, allow_nan=True), encoding="utf-8")
    manifest_path.write_text(json.dumps(manifest, indent=2, allow_nan=True), encoding="utf-8")
    print(
        f"[ns-harness] ternary cross-shell replay wrote {summary_path}, "
        f"{checks_path}, {manifest_path}"
    )
    print(
        "[ns-harness] ternary cross-shell replay summary: "
        f"route={checks.get('route_decision')} "
        f"dominant_state={checks.get('dominant_red_source_state')} "
        f"dominant_kind={checks.get('dominant_red_source_kind')} "
        f"promotion={checks.get('promotion_status')}"
    )


def _load_signed_ternary_flip_summary(path: Path) -> dict[str, Any]:
    if not path.exists():
        raise SystemExit(f"--replay-signed-ternary-flip-summary path does not exist: {path}")
    try:
        summary = json.loads(path.read_text(encoding="utf-8"))
    except json.JSONDecodeError as exc:
        raise SystemExit(f"{path} is not valid JSON: {exc}") from exc
    if not isinstance(summary, dict):
        raise SystemExit(f"{path} must contain a JSON object")
    missing = sorted(SIGNED_TERNARY_FLIP_REQUIRED_SUMMARY_FIELDS.difference(summary.keys()))
    if missing:
        raise SystemExit(f"{path} is missing signed ternary flip summary fields: {', '.join(missing)}")
    if summary.get("contract") != "ns_signed_ternary_flip_artifact":
        raise SystemExit(f"{path} contract is not ns_signed_ternary_flip_artifact")
    return summary


def _run_signed_ternary_flip_replay(args: argparse.Namespace) -> None:
    source = args.replay_signed_ternary_flip_summary
    source_summary = _load_signed_ternary_flip_summary(source)

    args.out_dir.mkdir(parents=True, exist_ok=True)
    summary_path = args.out_dir / "ns_signed_ternary_flip_summary.json"
    checks_path = args.out_dir / "ns_diagnostic_checks.json"
    manifest_path = args.out_dir / "ns_diagnostic_manifest.json"

    shutil.copyfile(source, summary_path)
    flip_copy = _copy_optional_sibling(source, args.out_dir, "ns_cross_shell_flip_balance.csv")
    net_copy = _copy_optional_sibling(source, args.out_dir, "ns_net_ternary_lyapunov.csv")
    bt_copy = _copy_optional_sibling(source, args.out_dir, "ns_bt_signed_flip_decay.csv")
    no2cycle_copy = _copy_optional_sibling(source, args.out_dir, "ns_no2cycle_diagnostic.csv")

    checks = {
        **source_summary,
        "signed_ternary_flip_replay_available": True,
        "diagnostic_mode": "sprint51_signed_ternary_flip_replay_from_gpu_summary",
        "signed_ternary_flip_summary_input": str(source),
        "diagnostic_backend": "gpu_artifact_replay",
        "physical_bridge_available": False,
        "source_truth_loaded": False,
        "material_parent_lineage_recomputed": False,
        "signed_ternary_flip_replay_promotes": False,
        "clay_promotion": False,
        "navier_stokes_promotion": False,
        "clay_navier_stokes_promoted": False,
        "pass": False,
        "promotion_status": "NO_PROMOTION_SIGNED_TERNARY_FLIP_REPLAY_DIAGNOSTIC",
        "receipt_alignment": "DASHI.Physics.Closure.ClaySprintFiftyOneSignedTernaryFlipAuditReceipt",
        "evidence_boundary": (
            "Sprint 51 replay consumes dashiCFD signed ternary flip summaries only. "
            "It records involution-aware balance, BT proxy signed decay, net residue "
            "Lyapunov diagnostics, and no-2-cycle diagnostics. It does not prove "
            "theorem-grade BT distance, signed source summability, net-residue "
            "Lyapunov closure, physical bridge, stretch absorption, no finite-time "
            "blowup, or Clay regularity."
        ),
        "signed_ternary_flip_summary_field_contract": sorted(SIGNED_TERNARY_FLIP_REQUIRED_SUMMARY_FIELDS),
    }
    manifest = {
        "source": str(source),
        "parameters": {
            "replay_mode": "sprint51_signed_ternary_flip_from_gpu_summary",
            "signed_ternary_flip_summary_input": str(source),
        },
        "diagnostic_mode": "sprint51_signed_ternary_flip_replay_from_gpu_summary",
        "signed_ternary_flip_balance_row_count": source_summary.get("cross_shell_flip_balance_row_count"),
        "signed_ternary_flip_bt_decay_row_count": source_summary.get("bt_signed_flip_decay_row_count"),
        "signed_ternary_flip_net_lyapunov_row_count": source_summary.get("net_ternary_lyapunov_row_count"),
        "signed_ternary_flip_no2cycle_row_count": source_summary.get("no2cycle_diagnostic_row_count"),
        "outputs": {
            "signed_ternary_flip_summary": str(summary_path),
            "cross_shell_flip_balance_csv": flip_copy,
            "net_ternary_lyapunov_csv": net_copy,
            "bt_signed_flip_decay_csv": bt_copy,
            "no2cycle_diagnostic_csv": no2cycle_copy,
            "checks": str(checks_path),
            "manifest": str(manifest_path),
        },
        "receipt_alignment": "DASHI.Physics.Closure.ClaySprintFiftyOneSignedTernaryFlipAuditReceipt",
        "evidence_boundary": checks["evidence_boundary"],
        "promotion_status": checks["promotion_status"],
        "clay_promotion": False,
        "navier_stokes_promotion": False,
    }
    checks_path.write_text(json.dumps(checks, indent=2, allow_nan=True), encoding="utf-8")
    manifest_path.write_text(json.dumps(manifest, indent=2, allow_nan=True), encoding="utf-8")
    print(
        f"[ns-harness] signed ternary flip replay wrote {summary_path}, "
        f"{checks_path}, {manifest_path}"
    )
    print(
        "[ns-harness] signed ternary flip replay summary: "
        f"route={checks.get('route_decision')} "
        f"imbalance_fraction={checks.get('signed_flip_imbalance_fraction_of_paired_flow')} "
        f"no2cycle_failures={checks.get('no2cycle_failure_count')} "
        f"promotion={checks.get('promotion_status')}"
    )


def _load_sprint52_material_no2cycle_summary(path: Path) -> dict[str, Any]:
    if not path.exists():
        raise SystemExit(f"--replay-sprint52-material-no2cycle-summary path does not exist: {path}")
    try:
        summary = json.loads(path.read_text(encoding="utf-8"))
    except json.JSONDecodeError as exc:
        raise SystemExit(f"{path} is not valid JSON: {exc}") from exc
    if not isinstance(summary, dict):
        raise SystemExit(f"{path} must contain a JSON object")
    missing = sorted(SPRINT52_MATERIAL_NO2CYCLE_REQUIRED_SUMMARY_FIELDS.difference(summary.keys()))
    if missing:
        raise SystemExit(f"{path} is missing Sprint 52 summary fields: {', '.join(missing)}")
    if summary.get("contract") != "ns_sprint52_material_no2cycle_artifact":
        raise SystemExit(f"{path} contract is not ns_sprint52_material_no2cycle_artifact")
    return summary


def _run_sprint52_material_no2cycle_replay(args: argparse.Namespace) -> None:
    source = args.replay_sprint52_material_no2cycle_summary
    source_summary = _load_sprint52_material_no2cycle_summary(source)

    args.out_dir.mkdir(parents=True, exist_ok=True)
    summary_path = args.out_dir / "ns_sprint52_material_no2cycle_summary.json"
    checks_path = args.out_dir / "ns_diagnostic_checks.json"
    manifest_path = args.out_dir / "ns_diagnostic_manifest.json"

    shutil.copyfile(source, summary_path)
    material_copy = _copy_optional_sibling(source, args.out_dir, "ns_material_source_resolution.csv")
    amplitude_copy = _copy_optional_sibling(source, args.out_dir, "ns_no2cycle_amplitude.csv")

    checks = {
        **source_summary,
        "sprint52_material_no2cycle_replay_available": True,
        "diagnostic_mode": "sprint52_material_no2cycle_replay_from_gpu_summary",
        "sprint52_material_no2cycle_summary_input": str(source),
        "diagnostic_backend": "gpu_artifact_replay",
        "physical_bridge_available": False,
        "source_truth_loaded": False,
        "material_parent_lineage_recomputed": False,
        "sprint52_material_no2cycle_replay_promotes": False,
        "clay_promotion": False,
        "navier_stokes_promotion": False,
        "clay_navier_stokes_promoted": False,
        "pass": False,
        "promotion_status": "NO_PROMOTION_SPRINT52_MATERIAL_NO2CYCLE_REPLAY_DIAGNOSTIC",
        "receipt_alignment": "DASHI.Physics.Closure.ClaySprintFiftyTwoMaterialNo2CycleAuditReceipt",
        "evidence_boundary": (
            "Sprint 52 replay consumes material-source/no-2-cycle summary artifacts only. "
            "It records Sprint 49 material-parent source closure and Sprint 52 material-packet "
            "cycle-amplitude calibration. It does not prove theorem-grade physical oscillation "
            "amplitude, weighted amplitude summability, physical bridge, stretch absorption, "
            "no finite-time blowup, or Clay regularity."
        ),
        "sprint52_material_no2cycle_summary_field_contract": sorted(
            SPRINT52_MATERIAL_NO2CYCLE_REQUIRED_SUMMARY_FIELDS
        ),
    }
    manifest = {
        "source": str(source),
        "parameters": {
            "replay_mode": "sprint52_material_no2cycle_from_gpu_summary",
            "sprint52_material_no2cycle_summary_input": str(source),
        },
        "diagnostic_mode": "sprint52_material_no2cycle_replay_from_gpu_summary",
        "material_source_resolution_row_count": source_summary.get("material_source_resolution_row_count"),
        "no2cycle_amplitude_row_count": source_summary.get("no2cycle_amplitude_row_count"),
        "outputs": {
            "sprint52_material_no2cycle_summary": str(summary_path),
            "material_source_resolution_csv": material_copy,
            "no2cycle_amplitude_csv": amplitude_copy,
            "checks": str(checks_path),
            "manifest": str(manifest_path),
        },
        "receipt_alignment": "DASHI.Physics.Closure.ClaySprintFiftyTwoMaterialNo2CycleAuditReceipt",
        "evidence_boundary": checks["evidence_boundary"],
        "promotion_status": checks["promotion_status"],
        "clay_promotion": False,
        "navier_stokes_promotion": False,
    }
    checks_path.write_text(json.dumps(checks, indent=2, allow_nan=True), encoding="utf-8")
    manifest_path.write_text(json.dumps(manifest, indent=2, allow_nan=True), encoding="utf-8")
    print(
        f"[ns-harness] Sprint 52 material/no2cycle replay wrote {summary_path}, "
        f"{checks_path}, {manifest_path}"
    )
    print(
        "[ns-harness] Sprint 52 replay summary: "
        f"route={checks.get('route_decision')} "
        f"material_gate={checks.get('does_material_source_gate_close')} "
        f"amplitude_gate={checks.get('does_no2cycle_amplitude_gate_close')} "
        f"promotion={checks.get('promotion_status')}"
    )


def _load_sprint53_no2cycle_physical_summary(path: Path) -> dict[str, Any]:
    if not path.exists():
        raise SystemExit(f"--replay-sprint53-no2cycle-physical-summary path does not exist: {path}")
    try:
        summary = json.loads(path.read_text(encoding="utf-8"))
    except json.JSONDecodeError as exc:
        raise SystemExit(f"{path} is not valid JSON: {exc}") from exc
    if not isinstance(summary, dict):
        raise SystemExit(f"{path} must contain a JSON object")
    missing = sorted(SPRINT53_NO2CYCLE_PHYSICAL_REQUIRED_SUMMARY_FIELDS.difference(summary.keys()))
    if missing:
        raise SystemExit(f"{path} is missing Sprint 53 summary fields: {', '.join(missing)}")
    if summary.get("contract") != "ns_sprint53_no2cycle_physical_artifact":
        raise SystemExit(f"{path} contract is not ns_sprint53_no2cycle_physical_artifact")
    return summary


def _run_sprint53_no2cycle_physical_replay(args: argparse.Namespace) -> None:
    source = args.replay_sprint53_no2cycle_physical_summary
    source_summary = _load_sprint53_no2cycle_physical_summary(source)

    args.out_dir.mkdir(parents=True, exist_ok=True)
    summary_path = args.out_dir / "ns_sprint53_no2cycle_summary.json"
    checks_path = args.out_dir / "ns_diagnostic_checks.json"
    manifest_path = args.out_dir / "ns_diagnostic_manifest.json"

    shutil.copyfile(source, summary_path)
    physical_copy = _copy_optional_sibling(source, args.out_dir, "ns_no2cycle_physical_amplitude.csv")
    cadence_copy = _copy_optional_sibling(source, args.out_dir, "ns_no2cycle_cadence_comparison.csv")
    lyapunov_copy = _copy_optional_sibling(source, args.out_dir, "ns_net_residue_physical_lyapunov.csv")

    checks = {
        **source_summary,
        "sprint53_no2cycle_physical_replay_available": True,
        "diagnostic_mode": "sprint53_no2cycle_physical_replay_from_gpu_summary",
        "sprint53_no2cycle_physical_summary_input": str(source),
        "diagnostic_backend": "gpu_artifact_replay",
        "physical_bridge_available": False,
        "source_truth_loaded": False,
        "material_parent_lineage_recomputed": False,
        "sprint53_no2cycle_physical_replay_promotes": False,
        "clay_promotion": False,
        "navier_stokes_promotion": False,
        "clay_navier_stokes_promoted": False,
        "pass": False,
        "promotion_status": "NO_PROMOTION_SPRINT53_NO2CYCLE_PHYSICAL_REPLAY_DIAGNOSTIC",
        "receipt_alignment": "DASHI.Physics.Closure.ClaySprintFiftyThreeNo2CyclePhysicalAmplitudeReceipt",
        "evidence_boundary": (
            "Sprint 53 replay consumes physical no-2-cycle amplitude summary artifacts only. "
            "It does not recompute truth snapshots, FFTs, material lineage, theorem-grade "
            "physical oscillation amplitude, weighted amplitude summability, physical bridge, "
            "stretch absorption, no finite-time blowup, or Clay regularity."
        ),
        "sprint53_no2cycle_physical_summary_field_contract": sorted(
            SPRINT53_NO2CYCLE_PHYSICAL_REQUIRED_SUMMARY_FIELDS
        ),
    }
    manifest = {
        "source": str(source),
        "parameters": {
            "replay_mode": "sprint53_no2cycle_physical_from_gpu_summary",
            "sprint53_no2cycle_physical_summary_input": str(source),
        },
        "diagnostic_mode": "sprint53_no2cycle_physical_replay_from_gpu_summary",
        "physical_no2cycle_row_count": source_summary.get("physical_no2cycle_row_count"),
        "physical_amplitude_row_count": source_summary.get("physical_amplitude_row_count"),
        "outputs": {
            "sprint53_no2cycle_physical_summary": str(summary_path),
            "no2cycle_physical_amplitude_csv": physical_copy,
            "no2cycle_cadence_comparison_csv": cadence_copy,
            "net_residue_physical_lyapunov_csv": lyapunov_copy,
            "checks": str(checks_path),
            "manifest": str(manifest_path),
        },
        "receipt_alignment": "DASHI.Physics.Closure.ClaySprintFiftyThreeNo2CyclePhysicalAmplitudeReceipt",
        "evidence_boundary": checks["evidence_boundary"],
        "promotion_status": checks["promotion_status"],
        "clay_promotion": False,
        "navier_stokes_promotion": False,
    }
    checks_path.write_text(json.dumps(checks, indent=2, allow_nan=True), encoding="utf-8")
    manifest_path.write_text(json.dumps(manifest, indent=2, allow_nan=True), encoding="utf-8")
    print(
        f"[ns-harness] Sprint 53 no2cycle physical replay wrote {summary_path}, "
        f"{checks_path}, {manifest_path}"
    )
    print(
        "[ns-harness] Sprint 53 replay summary: "
        f"route={checks.get('route_decision')} "
        f"physical_fraction={checks.get('physical_small_cycle_fraction')} "
        f"physical_gate={checks.get('does_physical_cycle_gate_close')} "
        f"promotion={checks.get('promotion_status')}"
    )


def _load_sprint54_cycle_amplitude_summary(path: Path) -> dict[str, Any]:
    if not path.exists():
        raise SystemExit(f"--replay-sprint54-cycle-amplitude-summary path does not exist: {path}")
    try:
        summary = json.loads(path.read_text(encoding="utf-8"))
    except json.JSONDecodeError as exc:
        raise SystemExit(f"{path} is not valid JSON: {exc}") from exc
    if not isinstance(summary, dict):
        raise SystemExit(f"{path} must contain a JSON object")
    missing = sorted(SPRINT54_CYCLE_AMPLITUDE_REQUIRED_SUMMARY_FIELDS.difference(summary.keys()))
    if missing:
        raise SystemExit(f"{path} is missing Sprint 54 summary fields: {', '.join(missing)}")
    if summary.get("contract") != "ns_sprint54_cycle_amplitude_artifact":
        raise SystemExit(f"{path} contract is not ns_sprint54_cycle_amplitude_artifact")
    return summary


def _run_sprint54_cycle_amplitude_replay(args: argparse.Namespace) -> None:
    source = args.replay_sprint54_cycle_amplitude_summary
    source_summary = _load_sprint54_cycle_amplitude_summary(source)

    args.out_dir.mkdir(parents=True, exist_ok=True)
    summary_path = args.out_dir / "ns_sprint54_cycle_amplitude_summary.json"
    checks_path = args.out_dir / "ns_diagnostic_checks.json"
    manifest_path = args.out_dir / "ns_diagnostic_manifest.json"

    shutil.copyfile(source, summary_path)
    stretch_copy = _copy_optional_sibling(source, args.out_dir, "ns_stretch_cycle_physical_amplitude.csv")
    cadence_copy = _copy_optional_sibling(source, args.out_dir, "ns_no2cycle_cadence_comparison.csv")

    checks = {
        **source_summary,
        "sprint54_cycle_amplitude_replay_available": True,
        "diagnostic_mode": "sprint54_cycle_amplitude_replay_from_gpu_summary",
        "sprint54_cycle_amplitude_summary_input": str(source),
        "diagnostic_backend": "gpu_artifact_replay",
        "physical_bridge_available": False,
        "source_truth_loaded": False,
        "material_parent_lineage_recomputed": False,
        "sprint54_cycle_amplitude_replay_promotes": False,
        "clay_promotion": False,
        "navier_stokes_promotion": False,
        "clay_navier_stokes_promoted": False,
        "pass": False,
        "promotion_status": "NO_PROMOTION_SPRINT54_CYCLE_AMPLITUDE_REPLAY_DIAGNOSTIC",
        "receipt_alignment": "DASHI.Physics.Closure.ClaySprintFiftyFourNo2CycleResolutionCadenceAuditReceipt",
        "evidence_boundary": (
            "Sprint 54 replay consumes no-2-cycle resolution/cadence summary artifacts only. "
            "It does not recompute truth snapshots, packet material lineage, theorem-grade "
            "packet-local stretch amplitudes, weighted amplitude summability, physical bridge, "
            "stretch absorption, no finite-time blowup, or Clay regularity."
        ),
        "sprint54_cycle_amplitude_summary_field_contract": sorted(
            SPRINT54_CYCLE_AMPLITUDE_REQUIRED_SUMMARY_FIELDS
        ),
    }
    manifest = {
        "source": str(source),
        "parameters": {
            "replay_mode": "sprint54_cycle_amplitude_from_gpu_summary",
            "sprint54_cycle_amplitude_summary_input": str(source),
        },
        "diagnostic_mode": "sprint54_cycle_amplitude_replay_from_gpu_summary",
        "cycle_amplitude_row_count": source_summary.get("cycle_amplitude_row_count"),
        "cadence_comparison_row_count": source_summary.get("cadence_comparison_row_count"),
        "outputs": {
            "sprint54_cycle_amplitude_summary": str(summary_path),
            "stretch_cycle_physical_amplitude_csv": stretch_copy,
            "no2cycle_cadence_comparison_csv": cadence_copy,
            "checks": str(checks_path),
            "manifest": str(manifest_path),
        },
        "receipt_alignment": checks["receipt_alignment"],
        "evidence_boundary": checks["evidence_boundary"],
        "promotion_status": checks["promotion_status"],
        "clay_promotion": False,
        "navier_stokes_promotion": False,
    }
    checks_path.write_text(json.dumps(checks, indent=2, allow_nan=True), encoding="utf-8")
    manifest_path.write_text(json.dumps(manifest, indent=2, allow_nan=True), encoding="utf-8")
    print(
        f"[ns-harness] Sprint 54 cycle amplitude replay wrote {summary_path}, "
        f"{checks_path}, {manifest_path}"
    )
    print(
        "[ns-harness] Sprint 54 replay summary: "
        f"route={checks.get('route_decision')} "
        f"cadence={checks.get('cadence_sensitivity')} "
        f"resolution={checks.get('resolution_sensitivity')} "
        f"promotion={checks.get('promotion_status')}"
    )


def _load_sprint55_lagrangian_action_summary(path: Path) -> dict[str, Any]:
    if not path.exists():
        raise SystemExit(f"--replay-sprint55-lagrangian-action-summary path does not exist: {path}")
    try:
        summary = json.loads(path.read_text(encoding="utf-8"))
    except json.JSONDecodeError as exc:
        raise SystemExit(f"{path} is not valid JSON: {exc}") from exc
    if not isinstance(summary, dict):
        raise SystemExit(f"{path} must contain a JSON object")
    missing = sorted(SPRINT55_LAGRANGIAN_ACTION_REQUIRED_SUMMARY_FIELDS.difference(summary.keys()))
    if missing:
        raise SystemExit(f"{path} is missing Sprint 55 summary fields: {', '.join(missing)}")
    if summary.get("contract") != "ns_sprint55_lagrangian_action_artifact":
        raise SystemExit(f"{path} contract is not ns_sprint55_lagrangian_action_artifact")
    return summary


def _run_sprint55_lagrangian_action_replay(args: argparse.Namespace) -> None:
    source = args.replay_sprint55_lagrangian_action_summary
    source_summary = _load_sprint55_lagrangian_action_summary(source)

    args.out_dir.mkdir(parents=True, exist_ok=True)
    summary_path = args.out_dir / "ns_sprint55_lagrangian_action_summary.json"
    checks_path = args.out_dir / "ns_diagnostic_checks.json"
    manifest_path = args.out_dir / "ns_diagnostic_manifest.json"

    shutil.copyfile(source, summary_path)
    action_copy = _copy_optional_sibling(source, args.out_dir, "ns_lagrangian_stretch_action.csv")
    hysteresis_copy = _copy_optional_sibling(source, args.out_dir, "ns_packet_action_hysteresis.csv")
    by_shell_copy = _copy_optional_sibling(source, args.out_dir, "ns_lagrangian_action_by_shell.csv")

    checks = {
        **source_summary,
        "sprint55_lagrangian_action_replay_available": True,
        "diagnostic_mode": "sprint55_lagrangian_action_replay_from_gpu_summary",
        "sprint55_lagrangian_action_summary_input": str(source),
        "diagnostic_backend": "gpu_artifact_replay",
        "physical_bridge_available": False,
        "source_truth_loaded": False,
        "material_parent_lineage_recomputed": False,
        "packet_local_masks_loaded": False,
        "sprint55_lagrangian_action_replay_promotes": False,
        "clay_promotion": False,
        "navier_stokes_promotion": False,
        "clay_navier_stokes_promoted": False,
        "pass": False,
        "promotion_status": "NO_PROMOTION_SPRINT55_LAGRANGIAN_ACTION_REPLAY_DIAGNOSTIC",
        "receipt_alignment": "DASHI.Physics.Closure.ClaySprintFiftyFiveLagrangianStretchActionAuditReceipt",
        "evidence_boundary": (
            "Sprint 55 replay consumes Lagrangian accumulated stretch-action summary artifacts only. "
            "It does not recompute truth snapshots, material lineage, packet masks, packet-local "
            "stretch action, weighted action summability, physical bridge, stretch absorption, "
            "no finite-time blowup, or Clay regularity."
        ),
        "sprint55_lagrangian_action_summary_field_contract": sorted(
            SPRINT55_LAGRANGIAN_ACTION_REQUIRED_SUMMARY_FIELDS
        ),
    }
    manifest = {
        "source": str(source),
        "parameters": {
            "replay_mode": "sprint55_lagrangian_action_from_gpu_summary",
            "sprint55_lagrangian_action_summary_input": str(source),
        },
        "diagnostic_mode": "sprint55_lagrangian_action_replay_from_gpu_summary",
        "lagrangian_action_row_count": source_summary.get("lagrangian_action_row_count"),
        "hysteresis_row_count": source_summary.get("hysteresis_row_count"),
        "action_summary_row_count": source_summary.get("action_summary_row_count"),
        "outputs": {
            "sprint55_lagrangian_action_summary": str(summary_path),
            "lagrangian_stretch_action_csv": action_copy,
            "packet_action_hysteresis_csv": hysteresis_copy,
            "lagrangian_action_by_shell_csv": by_shell_copy,
            "checks": str(checks_path),
            "manifest": str(manifest_path),
        },
        "receipt_alignment": checks["receipt_alignment"],
        "evidence_boundary": checks["evidence_boundary"],
        "promotion_status": checks["promotion_status"],
        "clay_promotion": False,
        "navier_stokes_promotion": False,
    }
    checks_path.write_text(json.dumps(checks, indent=2, allow_nan=True), encoding="utf-8")
    manifest_path.write_text(json.dumps(manifest, indent=2, allow_nan=True), encoding="utf-8")
    print(
        f"[ns-harness] Sprint 55 Lagrangian action replay wrote {summary_path}, "
        f"{checks_path}, {manifest_path}"
    )
    print(
        "[ns-harness] Sprint 55 replay summary: "
        f"route={checks.get('route_decision')} "
        f"action_fraction={checks.get('action_small_fraction')} "
        f"sigma={checks.get('sigma_action_fit')} "
        f"promotion={checks.get('promotion_status')}"
    )


def _load_sprint56_packet_local_action_summary(path: Path) -> dict[str, Any]:
    if not path.exists():
        raise SystemExit(f"--replay-sprint56-packet-local-action-summary path does not exist: {path}")
    try:
        summary = json.loads(path.read_text(encoding="utf-8"))
    except json.JSONDecodeError as exc:
        raise SystemExit(f"{path} is not valid JSON: {exc}") from exc
    if not isinstance(summary, dict):
        raise SystemExit(f"{path} must contain a JSON object")
    missing = sorted(SPRINT56_PACKET_LOCAL_ACTION_REQUIRED_SUMMARY_FIELDS.difference(summary.keys()))
    if missing:
        raise SystemExit(f"{path} is missing Sprint 56 summary fields: {', '.join(missing)}")
    if summary.get("contract") != "ns_sprint56_packet_local_action_artifact":
        raise SystemExit(f"{path} contract is not ns_sprint56_packet_local_action_artifact")
    return summary


def _run_sprint56_packet_local_action_replay(args: argparse.Namespace) -> None:
    source = args.replay_sprint56_packet_local_action_summary
    source_summary = _load_sprint56_packet_local_action_summary(source)

    args.out_dir.mkdir(parents=True, exist_ok=True)
    summary_path = args.out_dir / "ns_sprint56_packet_local_action_summary.json"
    checks_path = args.out_dir / "ns_diagnostic_checks.json"
    manifest_path = args.out_dir / "ns_diagnostic_manifest.json"

    shutil.copyfile(source, summary_path)
    action_copy = _copy_optional_sibling(source, args.out_dir, "ns_packet_local_lagrangian_action.csv")
    hysteresis_copy = _copy_optional_sibling(source, args.out_dir, "ns_packet_local_action_hysteresis.csv")
    direction_copy = _copy_optional_sibling(source, args.out_dir, "ns_direction_change_separation.csv")
    by_shell_copy = _copy_optional_sibling(source, args.out_dir, "ns_packet_local_action_by_shell.csv")

    checks = {
        **source_summary,
        "sprint56_packet_local_action_replay_available": True,
        "diagnostic_mode": "sprint56_packet_local_action_replay_from_gpu_summary",
        "sprint56_packet_local_action_summary_input": str(source),
        "diagnostic_backend": "gpu_artifact_replay",
        "physical_bridge_available": False,
        "source_truth_loaded": False,
        "material_parent_lineage_recomputed": False,
        "packet_local_masks_loaded": False,
        "sprint56_packet_local_action_replay_promotes": False,
        "clay_promotion": False,
        "navier_stokes_promotion": False,
        "clay_navier_stokes_promoted": False,
        "pass": False,
        "promotion_status": "NO_PROMOTION_SPRINT56_PACKET_LOCAL_ACTION_REPLAY_DIAGNOSTIC",
        "receipt_alignment": "DASHI.Physics.Closure.ClaySprintFiftySixPacketLocalStretchActionAuditReceipt",
        "evidence_boundary": (
            "Sprint 56 replay consumes packet-local accumulated action summary artifacts only. "
            "It does not recompute truth snapshots, reconstructed packet masks, material lineage, "
            "weighted action summability, physical bridge, stretch absorption, no finite-time "
            "blowup, or Clay regularity."
        ),
        "sprint56_packet_local_action_summary_field_contract": sorted(
            SPRINT56_PACKET_LOCAL_ACTION_REQUIRED_SUMMARY_FIELDS
        ),
    }
    manifest = {
        "source": str(source),
        "parameters": {
            "replay_mode": "sprint56_packet_local_action_from_gpu_summary",
            "sprint56_packet_local_action_summary_input": str(source),
        },
        "diagnostic_mode": "sprint56_packet_local_action_replay_from_gpu_summary",
        "packet_local_action_row_count": source_summary.get("packet_local_action_row_count"),
        "packet_local_hysteresis_row_count": source_summary.get("packet_local_hysteresis_row_count"),
        "direction_change_row_count": source_summary.get("direction_change_row_count"),
        "action_summary_row_count": source_summary.get("action_summary_row_count"),
        "outputs": {
            "sprint56_packet_local_action_summary": str(summary_path),
            "packet_local_lagrangian_action_csv": action_copy,
            "packet_local_action_hysteresis_csv": hysteresis_copy,
            "direction_change_separation_csv": direction_copy,
            "packet_local_action_by_shell_csv": by_shell_copy,
            "checks": str(checks_path),
            "manifest": str(manifest_path),
        },
        "receipt_alignment": checks["receipt_alignment"],
        "evidence_boundary": checks["evidence_boundary"],
        "promotion_status": checks["promotion_status"],
        "clay_promotion": False,
        "navier_stokes_promotion": False,
    }
    checks_path.write_text(json.dumps(checks, indent=2, allow_nan=True), encoding="utf-8")
    manifest_path.write_text(json.dumps(manifest, indent=2, allow_nan=True), encoding="utf-8")
    print(
        f"[ns-harness] Sprint 56 packet-local action replay wrote {summary_path}, "
        f"{checks_path}, {manifest_path}"
    )
    print(
        "[ns-harness] Sprint 56 replay summary: "
        f"route={checks.get('route_decision')} "
        f"action_fraction={checks.get('action_small_fraction')} "
        f"sigma={checks.get('sigma_packet_local_action_fit')} "
        f"promotion={checks.get('promotion_status')}"
    )


def _load_sprint57_vessel_action_summary(path: Path) -> dict[str, Any]:
    if not path.exists():
        raise SystemExit(f"--replay-sprint57-vessel-action-summary path does not exist: {path}")
    try:
        summary = json.loads(path.read_text(encoding="utf-8"))
    except json.JSONDecodeError as exc:
        raise SystemExit(f"{path} is not valid JSON: {exc}") from exc
    if not isinstance(summary, dict):
        raise SystemExit(f"{path} must contain a JSON object")
    missing = sorted(SPRINT57_VESSEL_ACTION_REQUIRED_SUMMARY_FIELDS.difference(summary.keys()))
    if missing:
        raise SystemExit(f"{path} is missing Sprint 57 summary fields: {', '.join(missing)}")
    if summary.get("contract") != "ns_sprint57_vessel_action_reconciliation_artifact":
        raise SystemExit(f"{path} contract is not ns_sprint57_vessel_action_reconciliation_artifact")
    return summary


def _run_sprint57_vessel_action_replay(args: argparse.Namespace) -> None:
    source = args.replay_sprint57_vessel_action_summary
    source_summary = _load_sprint57_vessel_action_summary(source)

    args.out_dir.mkdir(parents=True, exist_ok=True)
    summary_path = args.out_dir / "ns_sprint57_vessel_action_reconciliation_summary.json"
    checks_path = args.out_dir / "ns_diagnostic_checks.json"
    manifest_path = args.out_dir / "ns_diagnostic_manifest.json"

    shutil.copyfile(source, summary_path)
    by_time_copy = _copy_optional_sibling(source, args.out_dir, "ns_vessel_action_reconciliation_by_time.csv")
    summary_csv_copy = _copy_optional_sibling(source, args.out_dir, "ns_vessel_action_reconciliation_summary.csv")

    checks = {
        **source_summary,
        "sprint57_vessel_action_replay_available": True,
        "diagnostic_mode": "sprint57_vessel_action_replay_from_gpu_summary",
        "sprint57_vessel_action_summary_input": str(source),
        "diagnostic_backend": "gpu_artifact_replay",
        "physical_bridge_available": False,
        "source_truth_loaded": False,
        "material_parent_lineage_recomputed": False,
        "packet_local_masks_loaded": False,
        "global_vessel_action_recomputed": False,
        "sprint57_vessel_action_replay_promotes": False,
        "packet_action_reconstructs_global_stretch_proved": False,
        "ultrametric_reassignment_proved": False,
        "weighted_packet_local_action_summability_proved": False,
        "clay_promotion": False,
        "navier_stokes_promotion": False,
        "clay_navier_stokes_promoted": False,
        "pass": False,
        "promotion_status": "NO_PROMOTION_SPRINT57_VESSEL_ACTION_REPLAY_DIAGNOSTIC",
        "receipt_alignment": "DASHI.Physics.Closure.ClaySprintFiftySevenVesselActionReconciliationReceipt",
        "evidence_boundary": (
            "Sprint 57 replay consumes vessel/action reconciliation summary artifacts only. "
            "It does not recompute truth snapshots, packet masks, material lineage, BT "
            "reassignment, weighted action summability, physical bridge, stretch absorption, "
            "no finite-time blowup, or Clay regularity."
        ),
        "sprint57_vessel_action_summary_field_contract": sorted(
            SPRINT57_VESSEL_ACTION_REQUIRED_SUMMARY_FIELDS
        ),
    }
    manifest = {
        "source": str(source),
        "parameters": {
            "replay_mode": "sprint57_vessel_action_from_gpu_summary",
            "sprint57_vessel_action_summary_input": str(source),
        },
        "diagnostic_mode": "sprint57_vessel_action_replay_from_gpu_summary",
        "time_window_count": source_summary.get("time_window_count"),
        "assignment_scheme": source_summary.get("assignment_scheme"),
        "outputs": {
            "sprint57_vessel_action_summary": str(summary_path),
            "vessel_action_reconciliation_by_time_csv": by_time_copy,
            "vessel_action_reconciliation_summary_csv": summary_csv_copy,
            "checks": str(checks_path),
            "manifest": str(manifest_path),
        },
        "receipt_alignment": checks["receipt_alignment"],
        "evidence_boundary": checks["evidence_boundary"],
        "promotion_status": checks["promotion_status"],
        "clay_promotion": False,
        "navier_stokes_promotion": False,
    }
    checks_path.write_text(json.dumps(checks, indent=2, allow_nan=True), encoding="utf-8")
    manifest_path.write_text(json.dumps(manifest, indent=2, allow_nan=True), encoding="utf-8")
    print(
        f"[ns-harness] Sprint 57 vessel action replay wrote {summary_path}, "
        f"{checks_path}, {manifest_path}"
    )
    print(
        "[ns-harness] Sprint 57 replay summary: "
        f"route={checks.get('route_decision')} "
        f"epsilon_covered={checks.get('epsilon_raw_positive_vs_covered')} "
        f"epsilon_global={checks.get('epsilon_raw_positive_vs_global')} "
        f"promotion={checks.get('promotion_status')}"
    )


def _load_sprint58_normalized_action_inflation_summary(path: Path) -> dict[str, Any]:
    if not path.exists():
        raise SystemExit(f"--replay-sprint58-normalized-action-inflation-summary path does not exist: {path}")
    try:
        summary = json.loads(path.read_text(encoding="utf-8"))
    except json.JSONDecodeError as exc:
        raise SystemExit(f"{path} is not valid JSON: {exc}") from exc
    if not isinstance(summary, dict):
        raise SystemExit(f"{path} must contain a JSON object")
    missing = sorted(SPRINT58_NORMALIZED_ACTION_INFLATION_REQUIRED_SUMMARY_FIELDS.difference(summary.keys()))
    if missing:
        raise SystemExit(f"{path} is missing Sprint 58 summary fields: {', '.join(missing)}")
    if summary.get("contract") != "ns_sprint58_normalized_action_inflation_artifact":
        raise SystemExit(f"{path} contract is not ns_sprint58_normalized_action_inflation_artifact")
    return summary


def _run_sprint58_normalized_action_inflation_replay(args: argparse.Namespace) -> None:
    source = args.replay_sprint58_normalized_action_inflation_summary
    source_summary = _load_sprint58_normalized_action_inflation_summary(source)

    args.out_dir.mkdir(parents=True, exist_ok=True)
    summary_path = args.out_dir / "ns_sprint58_normalized_action_inflation_summary.json"
    checks_path = args.out_dir / "ns_diagnostic_checks.json"
    manifest_path = args.out_dir / "ns_diagnostic_manifest.json"

    shutil.copyfile(source, summary_path)
    packet_copy = _copy_optional_sibling(source, args.out_dir, "ns_normalized_action_inflation_packets.csv")
    by_time_copy = _copy_optional_sibling(source, args.out_dir, "ns_normalized_action_inflation_by_time.csv")

    checks = {
        **source_summary,
        "sprint58_normalized_action_inflation_replay_available": True,
        "diagnostic_mode": "sprint58_normalized_action_inflation_replay_from_gpu_summary",
        "sprint58_normalized_action_inflation_summary_input": str(source),
        "diagnostic_backend": "gpu_artifact_replay",
        "physical_bridge_available": False,
        "source_truth_loaded": False,
        "material_parent_lineage_recomputed": False,
        "packet_local_masks_loaded": False,
        "normalized_action_inflation_recomputed": False,
        "sprint58_normalized_action_inflation_replay_promotes": False,
        "packet_action_reconstruction_proved": False,
        "normalized_action_additivity_proved": False,
        "denominator_inflation_theorem_proved": False,
        "weighted_packet_action_summability_proved": False,
        "clay_promotion": False,
        "navier_stokes_promotion": False,
        "clay_navier_stokes_promoted": False,
        "pass": False,
        "promotion_status": "NO_PROMOTION_SPRINT58_NORMALIZED_ACTION_INFLATION_REPLAY_DIAGNOSTIC",
        "receipt_alignment": "DASHI.Physics.Closure.ClaySprintFiftyEightNormalizedActionInflationReceipt",
        "evidence_boundary": (
            "Sprint 58 replay consumes normalized packet-action inflation artifacts only. "
            "It does not recompute truth snapshots, packet masks, material lineage, "
            "normalization additivity, denominator inflation theorem, weighted action "
            "summability, physical bridge, stretch absorption, no finite-time blowup, "
            "or Clay regularity."
        ),
        "sprint58_normalized_action_inflation_summary_field_contract": sorted(
            SPRINT58_NORMALIZED_ACTION_INFLATION_REQUIRED_SUMMARY_FIELDS
        ),
    }
    manifest = {
        "source": str(source),
        "parameters": {
            "replay_mode": "sprint58_normalized_action_inflation_from_gpu_summary",
            "sprint58_normalized_action_inflation_summary_input": str(source),
        },
        "diagnostic_mode": "sprint58_normalized_action_inflation_replay_from_gpu_summary",
        "time_window_count": source_summary.get("time_window_count"),
        "packet_inflation_row_count": source_summary.get("packet_inflation_row_count"),
        "outputs": {
            "sprint58_normalized_action_inflation_summary": str(summary_path),
            "normalized_action_inflation_packets_csv": packet_copy,
            "normalized_action_inflation_by_time_csv": by_time_copy,
            "checks": str(checks_path),
            "manifest": str(manifest_path),
        },
        "receipt_alignment": checks["receipt_alignment"],
        "evidence_boundary": checks["evidence_boundary"],
        "promotion_status": checks["promotion_status"],
        "clay_promotion": False,
        "navier_stokes_promotion": False,
    }
    checks_path.write_text(json.dumps(checks, indent=2, allow_nan=True), encoding="utf-8")
    manifest_path.write_text(json.dumps(manifest, indent=2, allow_nan=True), encoding="utf-8")
    print(
        f"[ns-harness] Sprint 58 normalized action inflation replay wrote {summary_path}, "
        f"{checks_path}, {manifest_path}"
    )
    print(
        "[ns-harness] Sprint 58 replay summary: "
        f"route={checks.get('route_decision')} "
        f"ratio_covered={checks.get('sum_ratios_over_ratio_of_sums_covered')} "
        f"low_denominator_fraction={checks.get('low_enstrophy_denominator_fraction')} "
        f"promotion={checks.get('promotion_status')}"
    )


def main() -> None:
    args = parse_args()
    if args.replay_sprint58_normalized_action_inflation_summary is not None:
        _run_sprint58_normalized_action_inflation_replay(args)
        return
    if args.replay_sprint57_vessel_action_summary is not None:
        _run_sprint57_vessel_action_replay(args)
        return
    if args.replay_sprint56_packet_local_action_summary is not None:
        _run_sprint56_packet_local_action_replay(args)
        return
    if args.replay_sprint55_lagrangian_action_summary is not None:
        _run_sprint55_lagrangian_action_replay(args)
        return
    if args.replay_sprint54_cycle_amplitude_summary is not None:
        _run_sprint54_cycle_amplitude_replay(args)
        return
    if args.replay_sprint53_no2cycle_physical_summary is not None:
        _run_sprint53_no2cycle_physical_replay(args)
        return
    if args.replay_sprint52_material_no2cycle_summary is not None:
        _run_sprint52_material_no2cycle_replay(args)
        return
    if args.replay_signed_ternary_flip_summary is not None:
        _run_signed_ternary_flip_replay(args)
        return
    if args.replay_ternary_cross_shell_summary is not None:
        _run_ternary_cross_shell_replay(args)
        return
    if args.replay_material_parent_summary is not None:
        _run_material_parent_replay(args)
        return
    if args.replay_packet_summary is not None:
        _run_replenishment_replay(args)
        return
    omega, velocity, steps, meta, source = _load_truth(args)
    if omega.ndim == 3:
        if args.diagnostic_backend == "gpu":
            raise SystemExit("--diagnostic-backend=gpu is only available for 3D vector truth snapshots")
        rows, summary, residue_preliminary = _rows_for_2d_scalar(omega, steps, meta, args)
    elif omega.ndim == 5 and omega.shape[-1] == 3:
        if args.diagnostic_backend == "gpu":
            rows, summary, residue_preliminary = _rows_for_3d_vector_gpu(omega, velocity, steps, meta, args)
        else:
            rows, summary, residue_preliminary = _rows_for_3d_vector(omega, velocity, steps, meta, args)
    else:
        raise SystemExit(
            "omega_snapshots must be 2D scalar (T,N,N) or 3D vector (T,N,N,N,3); "
            f"got shape {omega.shape}"
        )

    args.out_dir.mkdir(parents=True, exist_ok=True)
    csv_path = args.out_dir / "ns_diagnostic_table.csv"
    bridge_csv_path = args.out_dir / "ns_bridge_budget_table.csv"
    residue_audit_path = args.out_dir / "ns_residue_semantics_audit.csv"
    residue_wide_path = args.out_dir / "ns_residue_semantics_wide.csv"
    residue_theta_summary_path = args.out_dir / "ns_residue_theta_grid_summary.csv"
    budget_component_audit_path = args.out_dir / "ns_budget_component_audit.csv"
    source_decay_search_path = args.out_dir / "ns_source_decay_search.csv"
    source_decay_summary_path = args.out_dir / "ns_source_decay_summary.json"
    packet_transition_table_path = args.out_dir / "ns_packet_transition_table.csv"
    packet_transition_summary_csv_path = args.out_dir / "ns_packet_transition_summary.csv"
    packet_transition_summary_path = args.out_dir / "ns_packet_transition_summary.json"
    replenishment_decomposition_path = args.out_dir / "ns_replenishment_decomposition.csv"
    replenishment_summary_path = args.out_dir / "ns_replenishment_summary.json"
    checks_path = args.out_dir / "ns_diagnostic_checks.json"
    manifest_path = args.out_dir / "ns_diagnostic_manifest.json"
    _write_csv(csv_path, rows)
    bridge_rows, bridge_summary = _bridge_budget_rows(rows, meta)
    _write_bridge_budget_csv(bridge_csv_path, bridge_rows)
    residue_audit_rows, residue_theta_summary_rows, residue_audit_summary = _residue_audit_rows(residue_preliminary, meta, args)
    _write_residue_audit_csv(residue_audit_path, residue_audit_rows)
    residue_wide_rows = _write_residue_wide_csv(residue_wide_path, residue_audit_rows)
    _write_residue_theta_summary_csv(residue_theta_summary_path, residue_theta_summary_rows)
    budget_component_rows, budget_component_summary = _budget_component_audit_rows(residue_preliminary, meta, args)
    _write_budget_component_audit_csv(budget_component_audit_path, budget_component_rows)
    source_decay_rows, source_decay_summary = _source_decay_search_rows(residue_preliminary, meta, args)
    _write_source_decay_search_csv(source_decay_search_path, source_decay_rows)
    packet_transition_rows, packet_transition_summary_rows, packet_transition_summary = _packet_lineage_audit_rows(
        residue_preliminary,
        meta,
        args,
    )
    _write_packet_transition_csv(packet_transition_table_path, packet_transition_rows)
    _write_packet_transition_summary_csv(packet_transition_summary_csv_path, packet_transition_summary_rows)
    replenishment_rows, replenishment_summary = _replenishment_decomposition_rows(packet_transition_summary_rows, args)
    _write_replenishment_decomposition_csv(replenishment_decomposition_path, replenishment_rows)
    checks = _checks(rows, summary)
    checks.update(bridge_summary)
    checks.update(residue_audit_summary)
    checks.update(budget_component_summary)
    checks.update(source_decay_summary)
    checks.update(packet_transition_summary)
    checks.update(replenishment_summary)
    manifest = {
        "source": source,
        "meta": meta,
        "row_count": len(rows),
        "bridge_budget_row_count": len(bridge_rows),
        "residue_semantics_audit_row_count": len(residue_audit_rows),
        "residue_semantics_wide_row_count": len(residue_wide_rows),
        "residue_theta_grid_summary_row_count": len(residue_theta_summary_rows),
        "budget_component_audit_row_count": len(budget_component_rows),
        "source_decay_search_row_count": len(source_decay_rows),
        "packet_transition_table_row_count": len(packet_transition_rows),
        "packet_transition_summary_row_count": len(packet_transition_summary_rows),
        "replenishment_decomposition_row_count": len(replenishment_rows),
        "outputs": {
            "table": str(csv_path),
            "bridge_budget_table": str(bridge_csv_path),
            "residue_semantics_audit": str(residue_audit_path),
            "residue_semantics_wide": str(residue_wide_path),
            "residue_theta_grid_summary": str(residue_theta_summary_path),
            "budget_component_audit": str(budget_component_audit_path),
            "source_decay_search": str(source_decay_search_path),
            "source_decay_summary": str(source_decay_summary_path),
            "packet_transition_table": str(packet_transition_table_path),
            "packet_transition_summary_csv": str(packet_transition_summary_csv_path),
            "packet_transition_summary": str(packet_transition_summary_path),
            "replenishment_decomposition": str(replenishment_decomposition_path),
            "replenishment_summary": str(replenishment_summary_path),
            "checks": str(checks_path),
            "manifest": str(manifest_path),
        },
        "receipt_alignment": (
            "DASHI.Physics.Closure.ClaySprintFortyEightReplenishmentDecompositionReceipt"
            if bool(args.replenishment_decomposition_audit)
            else (
                "DASHI.Physics.Closure.ClaySprintFortySevenPacketLineageAuditReceipt"
                if bool(args.packet_lineage_audit)
                else (
                    "DASHI.Physics.Closure.ClaySprintFortySixSourceDecaySearchReceipt"
                    if bool(args.source_decay_search)
                    else (
                        "DASHI.Physics.Closure.ClaySprintFortyFiveBudgetComponentAuditReceipt"
                        if bool(args.budget_component_audit)
                        else "DASHI.Physics.Closure.ClaySprintFortyFourResidueSemanticsAuditReceipt"
                    )
                )
            )
        ),
        "evidence_boundary": "diagnostic harness only; no Navier-Stokes theorem or Clay promotion",
    }
    checks_path.write_text(json.dumps(checks, indent=2, allow_nan=True), encoding="utf-8")
    source_decay_summary_path.write_text(json.dumps(source_decay_summary, indent=2, allow_nan=True), encoding="utf-8")
    packet_transition_summary_path.write_text(json.dumps(packet_transition_summary, indent=2, allow_nan=True), encoding="utf-8")
    replenishment_summary_path.write_text(json.dumps(replenishment_summary, indent=2, allow_nan=True), encoding="utf-8")
    manifest_path.write_text(json.dumps(manifest, indent=2, allow_nan=True), encoding="utf-8")
    print(
        f"[ns-harness] wrote {csv_path}, {bridge_csv_path}, "
        f"{residue_audit_path}, {residue_wide_path}, {residue_theta_summary_path}, "
        f"{budget_component_audit_path}, {source_decay_search_path}, {source_decay_summary_path}, "
        f"{packet_transition_table_path}, {packet_transition_summary_csv_path}, "
        f"{packet_transition_summary_path}, {replenishment_decomposition_path}, "
        f"{replenishment_summary_path}, {checks_path}, {manifest_path}"
    )
    print(
        "[ns-harness] "
        f"mode={checks.get('diagnostic_mode')} pass={checks.get('pass')} "
        f"sup_C_K={checks.get('sup_C_K')} inf_budget_K={checks.get('inf_budget_K')} "
        f"promotion={checks.get('promotion_status')}"
    )


if __name__ == "__main__":
    main()
