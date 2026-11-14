#!/usr/bin/env python3
"""E2 physical source-constrained thermal neutron 14C visibility bound.

Given genuine verified UPPER flux, UPPER thermal cross-section, exposure,
target original N14 inventory, and a sample carbon-isotope normalization,
  N14(n,p)14C production <= N14 * flux_upper * sigma_upper * 1e-24 * dt.
Assume ALL newly made C14 stays in the measured pool (a strong conservative
assumption for THERMAL external-neutron production). Convert to an upper
sample pMC change only under supplied modern 14C:C ratio. Other energies,
tissue shielding, direct radiation, other reactions, sample contamination
and any emotional influence are NOT thereby excluded.

The example parameters are **hypothetical**: 2003 4 neutrons/cm2/hour is
a representative ambient MEAN, not a proven upper limit at a real human
tissue, 2026 thermal sigma 1.828 +/- .053 barn, sigma=1.828+3*.053 merely
an illustrative envelope, 1e20 N14 atoms, 1 gram carbon, 1.2e-12 modern
reference ratio, one year. Example is NOT an experimental exclusion.
"""
import argparse,json,math
NA=6.02214076e23
MOLAR_C=12.0107
BARN=1e-24

def bound(n14_atoms,thermal_flux_cm2_s_upper,thermal_sigma_barn_upper,
          exposure_seconds,carbon_mass_g,modern_c14_carbon_ratio):
    inputs=(n14_atoms,thermal_flux_cm2_s_upper,thermal_sigma_barn_upper,
            exposure_seconds,carbon_mass_g,modern_c14_carbon_ratio)
    if any(not math.isfinite(x) for x in inputs):
        raise ValueError("Nonfinite original physical input")
    if any(x<0 for x in inputs[:4]) or carbon_mass_g<=0 or not 0<modern_c14_carbon_ratio<1:
        raise ValueError("Invalid unsigned exposure/detection parameters")
    carbon_atoms=carbon_mass_g/MOLAR_C*NA
    products=n14_atoms*thermal_flux_cm2_s_upper*thermal_sigma_barn_upper*BARN*exposure_seconds
    return {
        "thermal_only_expected_14C_production_upper":products,
        "assumed_12_14_carbon_sample_atoms":carbon_atoms,
        "assumed_modern_C14_per_carbon":modern_c14_carbon_ratio,
        "conditional_delta_pMC_upper":100*products/(carbon_atoms*modern_c14_carbon_ratio),
        "other_energy_nuclear_reactions_bounded":False,
        "physically_measured_specimen":False,
        "within_band_upper_depends_on_verified_flux_and_xs_upper":True,
        "every_produced_C14_retained_in_sample":True,
    }

def synthetic_reference():
    sigma=1.828+3*.053
    r=bound(1e20,4/3600,sigma,365.25*86400,1,1.2e-12)
    assert 6<r["thermal_only_expected_14C_production_upper"]<8
    assert r["conditional_delta_pMC_upper"]<2e-8
    r.update({
        "status":"PASS, CONDITIONAL NUMERICAL EXAMPLE ONLY",
        "2026_thermal_measured_sigma_DOI":"10.1080/00223131.2026.2750299",
        "source_ambient_mean":"Dirk et al 2003 Terrestrial Thermal Neutrons, 4 n/cm²/hour is NOT an upper bound",
        "assumed_n14_atoms":1e20,"assumed_carbon_g":1,
        "assumed_sample_modern_ratio":1.2e-12,
        "assumed_exposure_years":1,
        "assumed_thermal_upper_flux_cm2_h":4,
        "assumed_cross_section_barn":sigma,
        "same_human_biology_or_nuclear_production_excluded":False,
    })
    return r

if __name__=="__main__":
    print(json.dumps(synthetic_reference(),indent=2))
