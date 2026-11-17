#!/usr/bin/env python3
"""FIELD LOOM: conservative engineering constraints, NOT a physical simulator.
Demo parameters are synthetic; no physical, clinical or psi data are supplied.
"""
from dataclasses import dataclass
from typing import FrozenSet, Optional

@dataclass(frozen=True)
class Mode:
    name: str
    modules: FrozenSet[str]
    is_human_connected: bool = False
    samples_for_human_use: bool = False
    laboratory_qualified: bool = False
    enclosed_hv: bool = False
    exhaust_validated: bool = False
    liquid_isolated: bool = False
    independently_measured: bool = False
    sham_measured: bool = False

@dataclass(frozen=True)
class Gate:
    permitted: bool
    issues: tuple[str, ...]
    classification: str

HV = frozenset({'plasma_reactor', 'corona_display', 'ewod_driver'})
CHEM = frozenset({'plasma_reactor', 'sample_chemistry'})

def audit(mode: Mode) -> Gate:
    x = mode.modules
    issues = []
    if 'plasma_reactor' in x and not mode.enclosed_hv:
        issues.append('Plasma reactor requires certified HV enclosure/interlocks.')
    if 'plasma_reactor' in x and not mode.exhaust_validated:
        issues.append('Plasma reactor requires gas capture and verified ventilation.')
    if x.intersection(HV) and not mode.laboratory_qualified:
        issues.append('High-field/electrode modules require qualified laboratory operation.')
    if x.intersection(CHEM) and not mode.liquid_isolated:
        issues.append('Chemical samples must be isolated from display and electronics.')
    if 'ferrofluid' in x and 'sample_chemistry' in x and not mode.liquid_isolated:
        issues.append('Optical ferrofluid cannot share the chemistry sample path.')
    if mode.is_human_connected and x.intersection(HV):
        issues.append('High-voltage or plasma mode forbidden while human-connected.')
    if mode.samples_for_human_use and x.intersection(CHEM):
        issues.append('Research plasma-activated liquids are not certified for human use.')
    if 'magnetic_coil' in x and 'biofeedback' in x and mode.is_human_connected:
        issues.append('Human sensing must be independent of field-actuation exposure mode.')
    if 'plasma_reactor' in x and 'ewod_driver' in x:
        issues.append('No simultaneous HV plasma and droplet-electrode operation in this revision.')
    if 'atmospheric_collector' in x and 'primary_power_supply' in x:
        issues.append('Atmospheric gradient is a measurement, not an authenticated power source.')
    if 'field_effect_claim' in x and not (mode.independently_measured and mode.sham_measured):
        issues.append('Field-specific effect claim requires measured exposure and matched sham.')
    label = 'eligible for research bench review' if not issues else 'blocked: missing safety/causal receipts'
    return Gate(not issues, tuple(issues), label)

@dataclass(frozen=True)
class EnergyLedger:
    """All joules belong to the SAME observation interval."""
    wall_input_j: float
    storage_draw_j: float
    assigned_mech_out_j: float
    assigned_chem_free_energy_j: float
    assigned_heat_out_j: float
    assigned_radiated_out_j: float
    storage_gain_j: float
    uncertainty_j: float

    def residual_j(self) -> float:
        return (self.wall_input_j + self.storage_draw_j
                - self.assigned_mech_out_j - self.assigned_chem_free_energy_j
                - self.assigned_heat_out_j - self.assigned_radiated_out_j
                - self.storage_gain_j)

    def audit(self) -> tuple[bool, str]:
        if any(v < 0 for v in vars(self).values()):
            return False, 'negative joules or uncertainty'
        if self.residual_j() < -self.uncertainty_j:
            return False, 'assigned output exceeds input; inspect measurements and boundary'
        return True, 'arithmetic admissible; unexplained residual is NOT closure'

@dataclass(frozen=True)
class Sample:
    batch_id: str
    volume_l: float
    nitrate_before_mol_l: Optional[float]
    nitrate_after_mol_l: Optional[float]

    def nitrate_delta_mol(self) -> Optional[float]:
        if self.nitrate_before_mol_l is None or self.nitrate_after_mol_l is None:
            return None
        if self.volume_l <= 0:
            raise ValueError('positive sample volume required')
        return self.volume_l * (self.nitrate_after_mol_l - self.nitrate_before_mol_l)

def _selftest() -> None:
    assert audit(Mode('field-optics', frozenset(
        {'magnetic_coil', 'ferrofluid', 'camera'}))).permitted
    assert not audit(Mode('unsafe', frozenset(
        {'plasma_reactor', 'sample_chemistry'}), is_human_connected=True)).permitted
    assert audit(Mode('sealed-water-chemistry', frozenset(
        {'plasma_reactor', 'sample_chemistry', 'camera'}),
        laboratory_qualified=True, enclosed_hv=True,
        exhaust_validated=True, liquid_isolated=True)).permitted
    assert not audit(Mode('misread-gradient', frozenset(
        {'atmospheric_collector', 'primary_power_supply'}))).permitted
    assert not audit(Mode('unmeasured-field-effect', frozenset({'field_effect_claim'}))).permitted
    assert audit(Mode('controlled-field-effect', frozenset({'field_effect_claim'}),
        independently_measured=True, sham_measured=True)).permitted
    good = EnergyLedger(100, 0, 2, 10, 70, 5, 0, 1)
    assert good.audit()[0] and good.residual_j() == 13
    assert not EnergyLedger(10, 0, 5, 20, 1, 0, 0, 0.1).audit()[0]
    value = Sample('synthetic', 0.1, 0.001, 0.003).nitrate_delta_mol()
    assert value is not None and abs(value - 0.0002) < 1e-15
    assert Sample('unmeasured', 0.1, None, None).nitrate_delta_mol() is None
    print('FIELD LOOM: 9 conservative gate/ledger/sample groups passed (synthetic)')

if __name__ == '__main__':
    _selftest()
