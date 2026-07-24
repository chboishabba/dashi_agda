#!/usr/bin/env python3
"""Emit the exact fail-closed ledger for the seven remaining periodic NS leaves."""
from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
from typing import Any

SCHEMA = "ns_seven_analytic_leaf_ledger.v1"


def digest(payload: Any) -> str:
    raw = json.dumps(payload, sort_keys=True, separators=(",", ":")).encode()
    return hashlib.sha256(raw).hexdigest()


def build() -> dict[str, Any]:
    leaves = [
        {
            "id": "official_carrier_uniform_harmonic",
            "completion": [
                "one Fourier normalization",
                "Parseval and shell Parseval",
                "Leray and Biot-Savart identification",
                "cutoff-uniform near-triad constant",
                "cutoff-uniform far-low row/column Schur constants",
                "cutoff-uniform far-high tail constant",
            ],
            "status": "conditional",
        },
        {
            "id": "compact_gamma_strict_expenditure",
            "completion": [
                "differentiate the concrete potential along Galerkin NS",
                "identify the Wall-I nonlinear ledger",
                "retain a strictly positive cutoff-uniform coercive margin",
                "bound forcing and switching remainder",
            ],
            "status": "conjectural",
        },
        {
            "id": "strict_normalized_boundary_signs",
            "completion": [
                "strict Gamma-floor inward sign",
                "strict normalized packet-fraction inward sign",
                "strict off-packet ceiling inward sign",
                "strict size-ceiling inward sign",
                "one common feasible parameter tuple",
            ],
            "status": "conjectural",
        },
        {
            "id": "universal_switch_control",
            "completion": [
                "uniform hysteresis gap",
                "time modulus or summable jump mechanism",
                "no immediate back-switch",
                "locally finite switching or finite total switch cost",
            ],
            "status": "conjectural",
        },
        {
            "id": "diffuse_spectrum_bkm",
            "completion": [
                "distributed reconstruction, classical criterion, or dissipation charging",
                "finite vorticity time integral on every diffuse interval",
            ],
            "status": "conjectural",
        },
        {
            "id": "exhaustive_zero_chart_diffuse",
            "completion": [
                "zero branch",
                "non-diffuse state selects a fully admissible normalized chart",
                "all chart failures enter a proved diffuse or direct-BKM mechanism",
            ],
            "status": "conjectural",
        },
        {
            "id": "cutoff_uniform_bound_and_limit_transport",
            "completion": [
                "one numerical bound independent of cutoff, shell, switches, and subsequence",
                "same selected Galerkin family",
                "fixed-shell convergence and finite-partial lower semicontinuity",
                "least-upper-bound weighted-envelope passage",
                "continuum vorticity reconstruction and BKM",
            ],
            "status": "conjectural",
        },
    ]
    reductions = [
        {
            "id": "biot_savart_transversality",
            "module": "NSPeriodicBiotSavartTransversality.agda",
            "result": "Biot-Savart velocity is transverse from dot-scale and cross orthogonality",
            "status": "machine_checked_reduction",
        },
        {
            "id": "strict_dissipation_margin",
            "module": "NSPeriodicStrictDissipationMargin.agda",
            "result": "near plus far-low plus far-high plus named strict margin is below viscosity",
            "status": "machine_checked_reduction",
        },
        {
            "id": "strict_margin_expenditure_adapter",
            "module": "NSPeriodicIntegratedExpenditureStrictMarginAdapter.agda",
            "result": "the named strict margin constructs the Wall-II budget comparison, weighted-shell bound, vorticity bound, and BKM endpoint",
            "status": "machine_checked_reduction",
        },
        {
            "id": "packet_fraction_quotient_sign",
            "module": "NSPeriodicPacketFractionQuotientSign.agda",
            "result": "positive quotient numerator and positive total-energy square imply inward packet-fraction derivative",
            "status": "machine_checked_reduction",
        },
        {
            "id": "common_boundary_parameters",
            "module": "NSPeriodicNormalizedBoundaryCommonParameters.agda",
            "result": "one admissible parameter tuple feeds all four normalized first-exit faces",
            "status": "machine_checked_reduction",
        },
        {
            "id": "hysteresis_separation",
            "module": "NSPeriodicHysteresisSeparation.agda",
            "result": "two-way switch gains require two hysteresis gaps below two score moduli",
            "status": "machine_checked_reduction",
        },
        {
            "id": "adaptive_switch_separation_adapter",
            "module": "NSPeriodicAdaptiveSwitchSeparationAdapter.agda",
            "result": "the double-gap separation theorem constructs the no-immediate-back-switch field in the adaptive switch package",
            "status": "machine_checked_reduction",
        },
        {
            "id": "diffuse_dissipation_charging",
            "module": "NSPeriodicDiffuseDissipationCharging.agda",
            "result": "absorbed diffuse dissipation charge plus finite remainder gives finite vorticity expenditure",
            "status": "machine_checked_reduction",
        },
        {
            "id": "diffuse_dissipation_route_adapter",
            "module": "NSPeriodicDiffuseDissipationRouteAdapter.agda",
            "result": "the dissipation-charge theorem concretely inhabits the diffuse BKM dispatcher",
            "status": "machine_checked_reduction",
        },
        {
            "id": "zero_chart_diffuse_selection",
            "module": "NSPeriodicZeroChartDiffuseSelection.agda",
            "result": "nondiffuse large packet must yield an admissible chart or direct BKM control",
            "status": "machine_checked_reduction",
        },
        {
            "id": "extended_coverage_bkm",
            "module": "NSPeriodicExtendedCoverageBKM.agda",
            "result": "zero, chart, diffuse, and direct-BKM branches map to one vorticity-control endpoint",
            "status": "machine_checked_reduction",
        },
        {
            "id": "weighted_envelope_limit_transport",
            "module": "NSPeriodicWeightedEnvelopeLimitTransport.agda",
            "result": "finite partial bounds plus least-upper-bound reconstruction transport the weighted envelope and vorticity bound",
            "status": "machine_checked_reduction",
        },
        {
            "id": "weighted_envelope_continuum_adapter",
            "module": "NSPeriodicWeightedEnvelopeContinuumAdapter.agda",
            "result": "weighted-envelope transport supplies the continuum vorticity premise used by BKM",
            "status": "machine_checked_reduction",
        },
    ]
    payload: dict[str, Any] = {
        "schema": SCHEMA,
        "dependency_order": [
            "official_carrier_uniform_harmonic",
            "compact_gamma_strict_expenditure",
            "strict_normalized_boundary_signs",
            "universal_switch_control",
            "diffuse_spectrum_bkm",
            "exhaustive_zero_chart_diffuse",
            "cutoff_uniform_bound_and_limit_transport",
        ],
        "leaves": leaves,
        "machine_checked_reductions": reductions,
        "coherence": {
            "same_official_fourier_carrier": True,
            "same_adaptive_trajectory": True,
            "same_selected_galerkin_family": True,
            "one_common_boundary_parameter_tuple": True,
        },
        "negative_findings_preserved": {
            "raw_multiplier_gain_is_full_far_low_bound": False,
            "static_compact_gamma_implies_adjacent_contraction": False,
            "absolute_packet_floor_is_invariant": False,
            "per_cutoff_finiteness_is_uniform_bound": False,
            "aubin_lions_l2_directly_transports_l1_linf_vorticity": False,
            "nondiffuse_automatically_implies_chart_admissible": False,
        },
        "promotion": {
            "seven_leaves_inhabited": False,
            "unconditional_periodic_navier_stokes": False,
            "clay_submission": False,
        },
    }
    payload["sha256"] = digest(payload)
    return payload


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--output-json", type=Path, required=True)
    parser.add_argument("--pretty", action="store_true")
    args = parser.parse_args()
    payload = build()
    args.output_json.parent.mkdir(parents=True, exist_ok=True)
    text = json.dumps(payload, sort_keys=True, indent=2 if args.pretty else None) + "\n"
    args.output_json.write_text(text, encoding="utf-8")
    print(text, end="")


if __name__ == "__main__":
    main()
