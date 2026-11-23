#!/usr/bin/env python3
"""SURA 2026 -> existing Filsinger finite Maxwell-Lorentz ADE source port.

Source: A. A. Chernyshov and collaborators, "HF Heating Effects as Seen From
Below and Above: First Results of Joint SURA-Ionosfera-M Experiment",
Geophysical Research Letters 53, e2026GL123503 (2026),
DOI 10.1029/2026GL123503; experiment 2025-08-20.

Original field measurements and interpretation remain credited to original
investigators. This independent DASHI adaptor uses their published pump clock
and qualitative spectral bands, but every ADE coefficient and source current
is synthetic and dimensionless. Neither a plasma constitutive derivation nor
receiver power measurement is implied. No CI or Agda acceptance is claimed.
"""
import json
import sympy as S
from smith_filsinger_lorentz_ade_sympy import (
    generator, exact_midpoint, synthetic_cycle_work_receipt, LorentzMaterial,
)

PAPER = {
    "doi": "10.1029/2026GL123503",
    "pump_frequency_hz": 5350000,
    "pump_mode": "O-mode",
    "erp_watt_approx": 150000000,
    "erp_is_not_transmitter_electrical_input": True,
    "pump_utc_start": "18:01",
    "on_minutes": 8,
    "off_minutes": 4,
    "satellite_overpass_utc": "18:41",
    "topside_altitude_km_approx": 820,
    "red_airglow_altitude_km": [300, 305],
    "TEC_depletion_fraction_approx": "1/20",
    "NVK_sample_hz": 46875,
    "NVK_fundamental_band_khz": [8, 9],
    "NVK_second_band_khz": [17, 18],
    "data_url": "https://links.cosmos.ru/87-3f-d4-49",
}


def minutes(utc):
    hour, minute = map(int, utc.split(":"))
    if not (0 <= hour <= 23 and 0 <= minute <= 59):
        raise ValueError("invalid UTC time")
    return 60 * hour + minute


def pump_active(utc):
    elapsed = minutes(utc) - minutes(PAPER["pump_utc_start"])
    if elapsed < 0:
        return False
    return (elapsed % 12) < 8


def exact_spectral_checks():
    first = S.Interval(8, 9)
    second_half = S.Interval(S.Rational(17, 2), 9)
    consistent = first.intersect(second_half)
    assert consistent == S.Interval(S.Rational(17, 2), 9)
    nyquist = S.Rational(PAPER["NVK_sample_hz"], 2)
    assert nyquist > 18000
    assert PAPER["pump_frequency_hz"] > nyquist
    assert pump_active("18:01") and pump_active("18:41")
    assert not pump_active("18:09") and not pump_active("18:45")
    assert sum(pump_active(f"18:{i:02d}") for i in range(1, 25)) == 16
    return {"on_at_overpass": True,
            "off_at_18_45": True,
            "on_count_first_24_minutes": 16,
            "off_count_first_24_minutes": 8,
            "nyquist_hz": str(nyquist),
            "second_harmonic_compatible_fundamental_khz": str(consistent),
            "harmonic_compatibility_is_not_mechanism_proof": True}


def exact_inverse_rank():
    # q: physically effective (not antenna ERP) pump-to-plasma source strength.
    # a,b: transfer to two spectral observation bands.
    # ell: instrument leakage. A single leakage diagnostic is an idealized
    # separate measurement, NOT a report that SURA has such calibrated data.
    q, a, b, ell = S.symbols("q a b ell", real=True, nonzero=True)
    params = [q, a, b, ell]
    raw = S.Matrix([q*a + ell, q*b + ell])
    leakage_diagnostic = S.Matrix([q*a + ell, q*b + ell, ell])
    independently_metered = S.Matrix([q*a + ell, q*b + ell, ell, q])
    ranks = [m.jacobian(params).rank() for m in
             (raw, leakage_diagnostic, independently_metered)]
    assert ranks == [2, 3, 4], ranks
    gain = S.symbols("gain", real=True, nonzero=True)
    assert S.simplify((q*gain)*(a/gain) - q*a) == 0
    assert S.simplify((q*gain)*(b/gain) - q*b) == 0
    return {"observed_two_band_rank": 2,
            "with_independent_leakage_rank": 3,
            "with_leakage_and_effective_source_meter_rank": 4,
            "unknown_parameters": 4,
            "unbroken_source_gain_symmetry": True,
            "nominal_ERP_does_not_measure_q": True}


def exact_ade_port_fixture():
    # One existing finite Galerkin cell; 12 source-gated synthetic steps.
    # One model step represents one pump clock minute only by an illustrative
    # choice of dimensionless time units, NOT a 60-second calibrated plasma.
    load = S.Rational(1, 7)
    A, B, mass = generator(n=1, material=LorentzMaterial(),
                           load_conductance=load)
    initial = S.zeros(4, 1)
    state = initial
    steps = []
    pump_off_controller_exact_zero = True
    for minute in range(1, 13):
        active = pump_active(f"18:{minute:02d}")
        natural = S.Matrix([S.Rational(1, 5)])
        controller = S.Matrix([S.Rational(2, 3) if active else S.Integer(0)])
        entry = exact_midpoint(state, natural, controller, S.Rational(1, 8),
                               A, B, mass, load_conductance=load)
        assert entry["residual"] == 0
        if not active:
            pump_off_controller_exact_zero &= entry["controller_work"] == 0
        state = entry["z"]
        steps.append(entry)
    receipt = synthetic_cycle_work_receipt(initial, steps, mass)
    assert receipt["conservation_residual"] == 0
    assert pump_off_controller_exact_zero
    assert receipt["restored_all_4n_states"] is False
    assert receipt["physically_replenished_source_certified"] is False
    assert receipt["original_source_meter_present"] is False
    assert receipt["useful_load"] > 0
    return {"reuse": "smith_filsinger_lorentz_ade_sympy exact_midpoint and synthetic_cycle_work_receipt",
            "state_dimensions": 4,
            "steps": 12,
            "controller_on": 8,
            "controller_off": 4,
            "all_step_energy_residuals_exact_zero": True,
            "total_conservation_residual": str(receipt["conservation_residual"]),
            "off_window_controller_work_zero": True,
            "positive_synthetic_load_work": True,
            "full_state_return": False,
            "source_meter_present": False,
            "model_is_calibrated_to_sura": False}


def exact_time_space_design_rank():
    # SURA pump S, LAERT instrument on L, flux-tube inside T. A pass
    # observed entirely while S=1 cannot identify background vs pump
    # or T vs pump*T, even with L switching. Missing cells must be paid
    # by genuinely matched off-cycle and spatial controls, not invented.
    def features(s, l, t):
        return [1, s, l, t, s*t, s*l]
    one_pump_cycle = S.Matrix([features(1,l,t) for l in (0,1) for t in (0,1)])
    full_factorial = S.Matrix([features(s,l,t)
                               for s in (0,1) for l in (0,1) for t in (0,1)])
    assert one_pump_cycle.rank() == 3
    assert full_factorial.rank() == 6
    return {"single_pump_on_pass_rank": 3,
            "full_crossed_pump_LAERT_spatial_rank": 6,
            "total_conceptual_columns": 6,
            "requires_source_off_and_spatial_matches": True,
            "source_did_not_supply_this_regression": True}


def run():
    result = {"status": "PASS",
              "level": "EXACT_FINITE_FIXTURE_AND_SOURCE_METADATA_NOT_PLASMA_REPLAY",
              "source": PAPER,
              "source_clock_and_spectra": exact_spectral_checks(),
              "inverse_identifiability": exact_inverse_rank(),
              "pump_LAERT_spatial_design": exact_time_space_design_rank(),
              "existing_ADE_source_port": exact_ade_port_fixture(),
              "warning": "SURA ERP is not electric input or receiver power; no actual satellite time-series or Filsinger receiver measured."}
    print(json.dumps(result, indent=2, sort_keys=True))
    return result


if __name__ == "__main__":
    run()
