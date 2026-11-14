#!/usr/bin/env python3
"""C2 14N(n,p)14C cross-energy negative control.

Li et al. 2026 DOI 10.1080/00223131.2026.2750299: measured fit
sigma=A*E_eV^B only 0.0036--1.8 eV.
EPRI 2010 report 1021106 Table 2-2 (OECD-NEA JEF Report 14, 1994):
old evaluated 14-MeV cross sections. They are NOT modern measured events.
Do not use fitted-law extrapolation in an actual neutron rate.
"""
import json
from math import isfinite

A=.2706
B=-.5103
FIT_MIN=.0036
FIT_MAX=1.8
E_14MEV=14_000_000.
OLD_14MEV_BARN={"JEF-2.2":.04325,"ENDF/B-VI":.04447,
                "JENDL-3.2":.00420,"BROND-2":.05404,
                "CENDL-2":.04324}


def measured_fit(E):
    if not isfinite(E) or not FIT_MIN<=E<=FIT_MAX:
        raise ValueError("outside original 2026 experimentally supported range")
    return A*E**B


def main():
    try:
        measured_fit(E_14MEV)
    except ValueError:
        extrapolation_blocked=True
    else:
        raise AssertionError("High-energy extrapolation incorrectly admitted")
    bad=A*E_14MEV**B   # disallowed illustration ONLY; never physical value.
    assert .04325/bad>700
    assert max(OLD_14MEV_BARN.values())/min(OLD_14MEV_BARN.values())>12
    thermal_fit=measured_fit(.0253)
    assert abs(thermal_fit-1.76691)<1e-5
    return {
      "status":"PASS","2026_original_DOI":"10.1080/00223131.2026.2750299",
      "2026_measured_fit_valid_eV":[FIT_MIN,FIT_MAX],
      "2026_separate_thermal_observation_barn":1.828,
      "2026_thermal_sigma_barn":.053,
      "2026_thermal_fitted_barn":thermal_fit,
      "evaluated_legacy_source":"EPRI report 1021106 Table 2-2; JEF Report 14 (1994)",
      "legacy_14MeV_barn":OLD_14MEV_BARN,
      "old_library_spread_factor":max(OLD_14MEV_BARN.values())/min(OLD_14MEV_BARN.values()),
      "disallowed_14MeV_extrapolation_barn":bad,
      "JEF_vs_disallowed_factor":.04325/bad,
      "source_fit_extrapolation_rejected":extrapolation_blocked,
      "real_site_specific_full_energy_rate_established":False,
      "legacy_evaluation_not_new_measurement":True,
    }


if __name__=="__main__":
    print(json.dumps(main(),sort_keys=True,indent=2))
