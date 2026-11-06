#!/usr/bin/env python3
"""Quantitative evidence adapter for Zhang 2025 versus independent controls.

Each returned value is tagged with its actual epistemic type:
  reported_nominal_range, assumed_waveform_prediction,
  author_3sigma_screening_envelope, instrumental_resolution,
  distribution_free_conditional_ci, or not_identifiable.
It DOES NOT create an antigravity experimental/physical receipt.
"""
from __future__ import annotations

import argparse
import json
import math
import statistics
from dataclasses import dataclass
from pathlib import Path

MU0 = 4 * math.pi * 1e-7
G_NOMINAL = 9.80665
FREQ_HZ = 50.0
MAGNETIC_RANGE_T = (0.1, 0.5)
SAMPLE_MASS_G = {
    "epoxy": 1.5, "paper": .050, "ceramic": 1.5,
    "leaf": .125, "aluminium": 2.0, "pork_skin": .5,
}
ZHANG_TOROID = "Zhang-Xu-2025-18mm-toroid"
ZHANG_PATENT = "Zhang-Xiao-Li-2025-HV-vacuum-sphere"
PAIS = "Pais-2019-HFGWG"
DRESDEN_2024 = "Tajmar-Koessling-Neunzig-2024-steady"
DRESDEN_2026 = "Tajmar-Olek-Neunzig-2026-DC-3A"

# A selection from the paper's original Table 1. Units are not coerced.
# The ± notation belongs to the authors' 3σ screening discussion; the
# paper does not identify it as an SE of a population-effect estimator.
DRESDEN_ROWS = (
    ("PTFE toroid vertical", -4.1, 4.1, "nN", "1A; PTFE core"),
    ("PTFE toroid torque", -.37, .27, "nN m", "1A; PTFE core"),
    ("iron toroid vertical", 7.0, 6.4, "nN", "1A; iron core"),
    ("crossed coil vertical", 13.8, 6.8, "nN", "1A; PC core"),
    ("toroid pair PLA", -.2, 2.7, "nN", "2A; PLA; V/V"),
    ("PTFE capacitor horizontal", .39, .66, "nN", "10kV; PTFE"),
    ("heated varistor horizontal", -25., 5.3, "nN", "33V; heated ZnO; outgassing and photon-pressure confounds"),
)
PAPER_2024 = "https://pmc.ncbi.nlm.nih.gov/articles/PMC11339412/"
PAPER_2025 = "https://www.ahdvlp.cn/upload/file/2025/07/276879f4533b6c125.pdf"
PAPER_2026 = "https://doi.org/10.1142/S0217751X26501472"


def is_finite_number(x: object) -> bool:
    return type(x) in (int, float) and math.isfinite(x)


def report_2025() -> dict:
    b0, b1 = MAGNETIC_RANGE_T
    return {
        "apparatus_id": ZHANG_TOROID,
        "source": PAPER_2025,
        "source_kind": "same_authors_primary_report_not_independent_replication",
        "field_T": {"kind": "reported_approximate_nominal_range",
                    "lo": b0, "hi": b1},
        "mass_g": {"kind": "reported_sample_values", "values": SAMPLE_MASS_G,
                   "ratio_max_to_min": max(SAMPLE_MASS_G.values()) / min(SAMPLE_MASS_G.values())},
        "gradient_B2_T2_per_m": {"kind": "not_identifiable", "value": None},
        "measured_acceleration_m_per_s2": {"kind": "not_identifiable", "value": None},
        "measured_force_N": {"kind": "not_identifiable", "value": None},
        "observed_acceleration_95CI": {"kind": "not_identifiable", "value": None,
             "reason": "no per-sample calibrated trajectories, uncertainties or repeat-level data"},
        "conditional_sinusoidal_Bpeak_dBdt_peak_T_per_s": {
            "kind": "assumed_waveform_prediction_not_measurement",
            "assumption": "50 Hz pure sinusoid and reported B values denote peak amplitudes",
            "lo": 2 * math.pi * FREQ_HZ * b0,
            "hi": 2 * math.pi * FREQ_HZ * b1,
        },
        "conditional_magnetic_energy_density_J_per_m3": {
            "kind": "model_derived_local_field_energy_not_net_force",
            "assumption": "nominal local B values, vacuum mu0 for energy density",
            "lo": b0 ** 2 / (2 * MU0),
            "hi": b1 ** 2 / (2 * MU0),
        },
        "material_independence_testable": True,
        "material_independence_established_by_common_acceleration_CI": False,
        "consumer": "Zhang2025EMGravityPhysicalPromotionExact: documentary/source-only; no calibrated experimental receipt",
    }


def report_2024() -> dict:
    result = []
    for name, estimate, reported_pm, unit, condition in DRESDEN_ROWS:
        if reported_pm < 0 or not math.isfinite(estimate):
            raise ValueError("invalid source row")
        result.append({
            "test": name, "condition": condition,
            "estimate": estimate, "reported_plus_minus": reported_pm, "unit": unit,
            "uncertainty_semantics": "paper uses 3sigma noise decision; ± is not certified SE",
            "author_rule_3sigma_envelope": {
                "kind": "screening_envelope_not_formal_95CI",
                "lo": estimate - 3 * reported_pm,
                "hi": estimate + 3 * reported_pm,
                "contains_zero": estimate - 3 * reported_pm <= 0 <= estimate + 3 * reported_pm,
            },
            "formal_95CI": None,
            "same_apparatus_as_zhang_toroid": False,
            "same_apparatus_as_zhang_HV_patent": False,
        })
    return {
        "apparatus_id": DRESDEN_2024,
        "source": PAPER_2024,
        "regime": "multiple steady-field shielded vacuum controls, not 50Hz Zhang",
        "evidence_kind": "published_measurement_plus_minus_with_3sigma_noise_rule",
        "rows": result,
        "consumer": "AntigravityClaimTheoryComparisonExact: external negative comparator only; do not promote to same-apparatus comparison",
    }


def report_2026() -> dict:
    mass_resolution_kg = .1e-6  # 0.1 mg -> 1e-7 kg
    return {
        "apparatus_id": DRESDEN_2026, "source": PAPER_2026,
        "regime": "DC up to 3A, ambient pressure/water, not Zhang 50Hz or HV",
        "published_balance_mass_resolution_mg": .1,
        "nominal_force_equivalent_N": mass_resolution_kg * G_NOMINAL,
        "force_equivalent_kind": "instrument_resolution_not_statistical_ci",
        "statistical_95CI": None,
        "consumer": "GR comparator external sensitivity, not an empirical Zhang anomaly or same-source null",
    }


def report_patent_pais() -> list[dict]:
    return [
        {
            "apparatus_id": ZHANG_PATENT,
            "source": "https://patents.google.com/patent/US12417870B1/en",
            "nominal_VI_W": 50000 * 1e-5,
            "value_kind": "nominal electrical product_not_measured_input_power",
            "experimental_force_95CI": None,
            "physical_consumer": "patent-source only; no calibrated gravity or motion receipt",
        },
        {
            "apparatus_id": PAIS,
            "source": "https://patents.google.com/patent/US10322827B2/en",
            "value_kind": "proposed_HFGWG_no_measured_radiative_TT_signal",
            "experimental_GW_95CI": None,
            "physical_consumer": "GravitationalWaveTheoryTestBidiExact: theoretical/detector readout not a measured emitting device",
        },
    ]


@dataclass(frozen=True)
class PairedCIInput:
    deltas: tuple[float, ...]
    lower_hard_bound: float
    upper_hard_bound: float
    alpha: float
    repeated_independent_source_switches_declared: bool
    calibration_and_nuisance_bound_declared: bool
    same_apparatus_declared: bool
    evidence_locator: str
    data_kind: str


def conditional_hoeffding_ci(payload: PairedCIInput) -> dict:
    """IID bounded paired differences; distribution-free conditional 1-alpha CI.

    Data provenance, independent trials and support bounds are assertions, not
    proven by this function. A source-independent noise bound for unmodelled
    systematic errors is not supplied by Hoeffding.
    """
    if not payload.deltas:
        raise ValueError("paired observations required")
    if not 0 < payload.alpha < 1:
        raise ValueError("alpha must lie strictly between 0 and 1")
    if not all(is_finite_number(x) for x in
               (*payload.deltas, payload.lower_hard_bound, payload.upper_hard_bound)):
        raise ValueError("finite numbers required")
    if payload.lower_hard_bound >= payload.upper_hard_bound:
        raise ValueError("finite strict hard bounds required")
    if any(not payload.lower_hard_bound <= x <= payload.upper_hard_bound
           for x in payload.deltas):
        raise ValueError("observed value outside asserted hard bounds")
    if payload.data_kind not in ("synthetic", "real_unverified"):
        raise ValueError("explicit data_kind required")
    if not payload.evidence_locator.strip():
        raise ValueError("independent evidence locator required")
    if not (payload.repeated_independent_source_switches_declared and
            payload.calibration_and_nuisance_bound_declared and
            payload.same_apparatus_declared):
        return {"kind": "not_identifiable", "95CI": None,
                "reason": "missing independence, calibration/nuisance or same-apparatus contract"}
    n = len(payload.deltas)
    width = (payload.upper_hard_bound - payload.lower_hard_bound) * (
        math.sqrt(math.log(2 / payload.alpha) / (2 * n))
    )
    mean = statistics.fmean(payload.deltas)
    return {
        "kind": "distribution_free_conditional_ci_not_empirical_promotion",
        "data_kind": payload.data_kind,
        "n_independent_pairs_declared": n,
        "nominal_coverage": 1 - payload.alpha,
        "point_estimate": mean,
        "interval": [mean - width, mean + width],
        "interval_unit": "units_of_input_deltas",
        "independence_and_hard_bound_verified": False,
        "anomaly_or_gravity_established": False,
    }



def acceleration_interval_from_force(
    force_lo_N: float, force_hi_N: float,
    mass_lo_kg: float, mass_hi_kg: float,
) -> tuple[float, float]:
    """Conservative a=F/m interval; DOES NOT assume force is gravitational."""
    values = (force_lo_N, force_hi_N, mass_lo_kg, mass_hi_kg)
    if not all(is_finite_number(v) for v in values):
        raise ValueError("force and mass bounds must be finite numbers")
    if force_lo_N > force_hi_N or not 0 < mass_lo_kg <= mass_hi_kg:
        raise ValueError("ordered force and strictly positive mass intervals required")
    candidates = (
        force_lo_N / mass_lo_kg, force_lo_N / mass_hi_kg,
        force_hi_N / mass_lo_kg, force_hi_N / mass_hi_kg,
    )
    return min(candidates), max(candidates)


def conditional_material_independence_consumer(rows: list[dict]) -> dict:
    """Necessary interval consistency screen, not evidence for common gravity.

    Expects distinct samples in one apparatus and identical source protocol.
    Each supplied force interval must be from separately calibrated outcomes
    and ordinary-force subtraction; this utility cannot verify its provenance.
    """
    if len(rows) < 2:
        raise ValueError("at least two distinct material samples required")
    apparatuses = {row.get("apparatus_id") for row in rows}
    protocols = {row.get("protocol_id") for row in rows}
    samples = {row.get("sample_id") for row in rows}
    if len(apparatuses) != 1 or len(protocols) != 1 or len(samples) != len(rows):
        raise ValueError("same apparatus/protocol and distinct samples required")
    if None in apparatuses or None in protocols or None in samples:
        raise ValueError("apparatus, protocol and sample IDs required")
    intervals = []
    for row in rows:
        if not row.get("calibrated_force_and_ordinary_controls_declared", False):
            return {"kind": "not_identifiable", "reason": "force/ordinary controls missing"}
        if not str(row.get("data_locator", "")).strip():
            raise ValueError("row data locator required")
        v = acceleration_interval_from_force(
            row["force_lo_N"], row["force_hi_N"],
            row["mass_lo_kg"], row["mass_hi_kg"],
        )
        intervals.append({"sample_id": row["sample_id"],
                          "acceleration_interval_m_per_s2": [v[0], v[1]]})
    lower = max(x["acceleration_interval_m_per_s2"][0] for x in intervals)
    upper = min(x["acceleration_interval_m_per_s2"][1] for x in intervals)
    return {
        "kind": "necessary_interval_overlap_not_proof_of_gravitational_coupling",
        "samples": intervals,
        "shared_acceleration_interval": [lower, upper] if lower <= upper else None,
        "common_acceleration_rejected_by_intervals": lower > upper,
        "common_acceleration_established": False,
        "gravitational_mechanism_established": False,
    }


def full_report() -> dict:
    return {
        "schema": "Zhang2025QuantitativeConsumers/v1",
        "2025_toroid": report_2025(),
        "2024_independent_steady_null": report_2024(),
        "2026_independent_DC_null": report_2026(),
        "patent_and_Pais": report_patent_pais(),
        "promotion": {
            "same_object_empirical_anomaly_available": False,
            "verified_metric_response_available": False,
            "independent_Zhang_replication_available": False,
            "warning": "Numerical envelopes and model sensitivities do not construct empirical Agda physical receipts.",
        },
    }


def main() -> None:
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("--output", type=Path, help="optional source-bounded JSON report")
    args = p.parse_args()
    report = json.dumps(full_report(), ensure_ascii=False, sort_keys=True, indent=2) + "\n"
    if args.output:
        args.output.write_text(report, encoding="utf-8")
    else:
        print(report, end="")


if __name__ == "__main__":
    main()
