#!/usr/bin/env python3
"""Exact SI physical-scale enclosures for the *continuum* Gielis domain.

The selected unit-free Ω_3 is a proper subset of (-sqrt(2),sqrt(2))².
Dirichlet min-max gives lambda_1(Ω_3)>pi²/4>9/4, while the explicit
radial H_0^1 trial function gives lambda_1(Ω_3)<1273/264.

Scaling x->L x gives lambda_1(L Ω_3)=lambda_1(Ω_3)/L².
Thus for an *assumed, not measured* characteristic SI length
L in [L_low,L_high], all exact rational arithmetic gives

  9/(4 L_high²) < lambda_1(L Ω_3) <
       1273/(264 L_low²)  [m^-2].

Neither a physical resonant frequency nor any optical/gravity effect
follows without a constitutive wave-speed, boundary conditions and
physical geometry matching the assumed selected domain.
"""
from __future__ import annotations
from fractions import Fraction as Q
from pathlib import Path
import argparse
import json
from gielis_si_owner_adapter import canonical_speed_of_light_si, owner_receipt

LOW = Q(9,4)
HIGH = Q(1273,264)

def gielis_m3_physical_continuum_enclosure(length_low_m, length_high_m):
    lo=Q(str(length_low_m))
    hi=Q(str(length_high_m))
    if not (0<lo<=hi):
        raise ValueError("a positive ordered length interval is required")
    lower=LOW/(hi*hi)
    upper=HIGH/(lo*lo)
    assert lower<upper
    si=owner_receipt()
    return {
        "domain":"continuum scaled selected Gielis m=3 domain",
        "source_SI_owner":si["si_dimension_owner"],
        "length_low_m_exact":str(lo),
        "length_high_m_exact":str(hi),
        "first_dirichlet_eigenvalue_lower_m^-2_open":str(lower),
        "first_dirichlet_eigenvalue_upper_m^-2_open":str(upper),
        "both_eigenvalue_bounds_strict":True,
        "lambda_dimension_MLT":(0,-2,0),
        "proof":"Dirichlet square-domain monotonicity pi>3; H0^1 Rayleigh trial; dilation x↦Lx",
        "scale_interval_is_measured":False,
        "physical_resonant_frequency_inferred":False,
        "unitless_shape_physically_identified":False,
    }

def physical_scale_discrete_lambda_interval(
    lambda_low,lambda_high,length_low_m,length_high_m):
    """Transport E17 exact finite raster eigenvalue bounds: NOT continuum."""
    lam_lo=Q(str(lambda_low));lam_hi=Q(str(lambda_high))
    Llo=Q(str(length_low_m));Lhi=Q(str(length_high_m))
    if not (0<lam_lo<=lam_hi and 0<Llo<=Lhi):
        raise ValueError("positive lambda and length intervals needed")
    return {
        "model":"fixed finite-dimensional Dirichlet FD matrix, scaled spacing",
        "first_eigenvalue_lower_m^-2":str(lam_lo/(Lhi*Lhi)),
        "first_eigenvalue_upper_m^-2":str(lam_hi/(Llo*Llo)),
        "certified_finite_matrix_only":True,
        "continuum_fd_convergence_proved":False,
    }

def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--length-low-metres",default="99/100")
    parser.add_argument("--length-high-metres",default="101/100")
    parser.add_argument("--output")
    args=parser.parse_args()
    out=gielis_m3_physical_continuum_enclosure(
        args.length_low_metres,args.length_high_metres)
    data=json.dumps(out,indent=2,sort_keys=True)
    if args.output:
        Path(args.output).write_text(data+"\n")
    print(data)

if __name__=="__main__":
    main()
