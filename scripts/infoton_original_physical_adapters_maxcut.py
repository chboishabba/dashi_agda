#!/usr/bin/env python3
"""Same-object physical discrimination for January Walker's Infoton/P30 claims.

No original P30 implementation, certified device, experimental particle, or
metered data is supplied here.  Synthetic tests are not measurements.

Origin: Johl Brown / DASHI research integration. January Walker: hypothesis
source; Matthew Reece: published global gauge-group source.

Original DASHI physical owners (import and run them, never redefine them):
  DASHI/Physics/Gravity/KKQEDQCDHyperchargeBIDIExact.agda
  scripts/check_kk_e6_post_e21_u3_photon.py
  DASHI/Physics/Laws/{ThermodynamicStatisticalLaws,
    ConstantsMetrologyBoundary,ExistingPhysicsAdapter}.agda
  DASHI/Environment/DataCentreThermalReuseMetricBoundaryExact.agda
  scripts/datacentre_thermal_reuse_dispatch.py
"""
from dataclasses import dataclass
from decimal import Decimal, InvalidOperation
from fractions import Fraction
from math import log

K_B = Decimal("1.380649e-23")
C = Decimal("299792458")
LN2 = Decimal(str(log(2)))

# Integer sixths from DASHI.Physics.Gravity.KKQEDQCDHyperchargeBIDIExact.
# Not inferred from Fermi occupations: these are original SM gauge charges.
CHARGE_SIXTHS = {
    "up": 4, "charm": 4, "top": 4,
    "down": -2, "strange": -2, "bottom": -2,
    "electron": -6, "muon": -6, "tau": -6,
    "neutrino": 0,
}
COLOUR_TRIALITY = {"up": 1, "charm": 1, "top": 1,
                    "down": 1, "strange": 1, "bottom": 1,
                    "electron": 0, "muon": 0, "tau": 0, "neutrino": 0}


def global_u3_charge_residue(charge_sixths: int, triality: int) -> bool:
    """Existing original E6 U(3) necessary centre-descent congruence."""
    if charge_sixths % 2:
        return False  # 3 Q must be an integer
    return (triality + charge_sixths // 2) % 3 == 0


def original_charge_receipt():
    """Finite checksum; original repo 27-state source remains stronger owner."""
    assert all(global_u3_charge_residue(CHARGE_SIXTHS[k], COLOUR_TRIALITY[k])
               for k in CHARGE_SIXTHS)
    return dict(physical_multiplets=len(CHARGE_SIXTHS),
                up_sixths=CHARGE_SIXTHS["up"],
                down_sixths=CHARGE_SIXTHS["down"],
                electron_sixths=CHARGE_SIXTHS["electron"],
                neutrino_sixths=CHARGE_SIXTHS["neutrino"],
                original_27_physical_theorem_claimed_here=False)


def fermi_landauer_anchor(temperature_kelvin: Decimal):
    """FD anchor, for E-mu=kBT ln2, not a charge-generation mechanism."""
    if not temperature_kelvin.is_finite() or temperature_kelvin <= 0:
        raise ValueError("positive finite temperature is required")
    return Fraction(1, 3), Fraction(2, 3)


def landauer_erasure_floor_joule(temperature_kelvin: Decimal,
                                logically_erased_bits: int):
    """Only a lower bound for known irreversible erasure, not CPU power."""
    if not temperature_kelvin.is_finite() or temperature_kelvin <= 0:
        raise ValueError("temperature must be positive and finite")
    if not isinstance(logically_erased_bits, int) or logically_erased_bits < 0:
        raise ValueError("erased bit count must be a nonnegative integer")
    return K_B * temperature_kelvin * LN2 * logically_erased_bits


def landauer_mass_equivalent_kg(temperature_kelvin: Decimal):
    return landauer_erasure_floor_joule(temperature_kelvin, 1) / (C*C)


def source_rack_sensitivity_kw(fixed_fraction: Fraction,
                                original_kw: Fraction=Fraction(130),
                                source_operations_ratio: Fraction=Fraction(12264, 163)):
    """Conditional sensitivity, explicitly NOT physically observed savings."""
    if not 0 <= fixed_fraction <= 1 or original_kw <= 0 or source_operations_ratio < 1:
        raise ValueError("invalid domain")
    return original_kw * (fixed_fraction + (1-fixed_fraction) / source_operations_ratio)


@dataclass(frozen=True)
class MeasuredVerifiedService:
    """Physical metrology fields, not a synthetic gate/success flag.

    Measured values must come from a calibrated meter; constructing this class
    alone NEVER establishes that calibration, a real observation, or a P30 run.
    """
    source_receipt: str
    workload_sha256: str
    fault_corpus_sha256: str
    implementation_sha: str
    hardware_id: str
    calibration_receipt: str
    timestamp_utc: str
    verified_outputs: int
    measured_joules: Decimal
    measured_duration_s: Decimal
    site_water_l: Decimal | None = None
    recovered_heat_joules: Decimal | None = None
    error_correction_proof_receipt: str = ""

    def validate(self):
        for field_name in ("source_receipt", "workload_sha256", "fault_corpus_sha256",
                           "implementation_sha", "hardware_id", "calibration_receipt",
                           "timestamp_utc", "error_correction_proof_receipt"):
            if not getattr(self, field_name):
                raise ValueError(f"missing original evidence: {field_name}")
        if self.verified_outputs <= 0:
            raise ValueError("no verified completed work")
        for field_name in ("measured_joules", "measured_duration_s"):
            x = getattr(self, field_name)
            if not isinstance(x, Decimal) or not x.is_finite() or x <= 0:
                raise ValueError(f"invalid measured field: {field_name}")
        for field_name in ("site_water_l", "recovered_heat_joules"):
            x = getattr(self, field_name)
            if x is not None and (not isinstance(x, Decimal) or not x.is_finite() or x < 0):
                raise ValueError(f"invalid optional metering: {field_name}")

    def joules_per_verified_output(self):
        self.validate()
        return self.measured_joules / Decimal(self.verified_outputs)


def compare_measured_verified_service(baseline: MeasuredVerifiedService,
                                      proposed: MeasuredVerifiedService):
    """Reject incomparable workloads/fault models; data alone cannot verify source authenticity."""
    baseline.validate(); proposed.validate()
    if baseline.workload_sha256 != proposed.workload_sha256:
        raise ValueError("different workload, cannot compare")
    if baseline.fault_corpus_sha256 != proposed.fault_corpus_sha256:
        raise ValueError("different integrity fault corpus, cannot compare")
    if baseline.verified_outputs != proposed.verified_outputs:
        raise ValueError("different completed outputs, cannot compare")
    if baseline.hardware_id != proposed.hardware_id:
        raise ValueError("different hardware: need explicit platform normalisation")
    b = baseline.joules_per_verified_output()
    p = proposed.joules_per_verified_output()
    return dict(baseline_j_per_output=b, proposed_j_per_output=p,
                ratio=b/p, energy_reduction_fraction=(b-p)/b,
                original_implementation_reproduced=False,
                independent_meter_authentication=False)


def measured_water_per_it_kwh(water_litres: Decimal | None,
                              it_energy_kwh: Decimal | None):
    """WUE needs water AND IT energy measured at the same facility boundary."""
    if water_litres is None or it_energy_kwh is None:
        raise ValueError("water or IT energy measurement missing")
    if (not water_litres.is_finite() or not it_energy_kwh.is_finite()
            or water_litres < 0 or it_energy_kwh <= 0):
        raise ValueError("invalid measured WUE inputs")
    return water_litres / it_energy_kwh


def use_existing_thermal_dispatch(it_kw: float, pue: float,
                                 concurrent_direct_mw: float,
                                 concurrent_high_mw: float):
    """Import the existing exact-source physical dispatch; do not copy its COP laws."""
    from datacentre_thermal_reuse_dispatch import Parameters, dispatch
    params = Parameters(it_mw=it_kw/1000, pue=pue)
    return dispatch(params, concurrent_direct_mw, concurrent_high_mw)


if __name__ == "__main__":
    import json
    print(json.dumps({"sm_charge": original_charge_receipt(),
                      "mass_at_300K_kg": str(landauer_mass_equivalent_kg(Decimal(300))),
                      "rack_conditional_kw_25pct_fixed": str(source_rack_sensitivity_kw(Fraction(1,4))),
                      "original_p30_measured": False}, indent=2))
