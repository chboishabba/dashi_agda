#!/usr/bin/env python3
"""GaAs/AlGaAs QW effective mass -> confinement energy discriminator.

Published source-inferred masses: Molenkamp et al PRB 38, 4314(R), 1988
DOI 10.1103/PhysRevB.38.4314 : HH [111] 0.70 m0; HH [001] 0.34 m0.
Original near-Gamma gamma theory [111]: 25/28=0.892857 m0.
Envelope precedent Eppenga and Schuurmans, Philips Technical Review 44(5)
(1988), 'Theory of the GaAs/AlGaAs quantum well', pp 137-149:
https://www.worldradiohistory.com/Archive-Company-Publications/Philips-Technical-Review/80s/Philips-Technical-Review-1988.pdf

This is an independent FINITE BARRIER envelope model only: it does NOT
reproduce the cited authors' actual QW spectra, measured well parameters,
8-band valence mixing, exciton binding or photovoltaic collection.
Uses explicit BenDaniel-Duke continuity, even ground state, constant masses.
"""
import json
import numpy as np
from scipy.optimize import brentq

HBAR=1.054571817e-34
M0=9.1093837139e-31
Q=1.602176634e-19

def infinite_ground_ev(mass_m0,width_nm):
    return (np.pi*HBAR)**2/(2*M0*mass_m0*(width_nm*1e-9)**2*Q)

def finite_ground_ev(mass_m0,width_nm,barrier_ev=.2,barrier_mass_m0=.9):
    """Symmetric finite square well even parity root, energy from well bottom.

    tan(k L/2)=(m_w/m_b)(kappa/k);
    both envelope and inverse-mass normal derivative continuous.
    Only first even root is sought, for an attractive well.
    """
    if not all(x>0 for x in (mass_m0,width_nm,barrier_ev,barrier_mass_m0)):
        raise ValueError("positive dimensions and material parameters required")
    bound=min(barrier_ev,infinite_ground_ev(mass_m0,width_nm))
    def residual(E):
        k=np.sqrt(2*mass_m0*M0*E*Q)/HBAR
        kap=np.sqrt(2*barrier_mass_m0*M0*(barrier_ev-E)*Q)/HBAR
        return np.tan(k*width_nm*1e-9/2)-mass_m0*kap/(barrier_mass_m0*k)
    low=1e-14
    hi=min(bound*(1-1e-12),barrier_ev*(1-1e-12))
    if residual(hi)<=0: raise RuntimeError("even ground state not bracketed")
    root=brentq(residual,low,hi,xtol=1e-15)
    return root

def run():
    tests=[]
    def check(name,ok):
        assert bool(ok),name
        tests.append(name)
    inferred=.7
    nominal=25/28
    check("exact 111 bulk nominal",abs(nominal-.8928571428571429)<1e-14)
    check("mass difference source",abs(nominal-inferred)>.19)
    checks={}
    for L in (5.,8.,10.):
        values={}
        for label,m in (("QW_inferred",inferred),("nominal_Gamma",nominal)):
            ei=infinite_ground_ev(m,L)
            ef=finite_ground_ev(m,L)
            check(f"{L}nm {label} finite positive",ef>0)
            check(f"{L}nm {label} finite below infinite",0<ef<ei)
            check(f"{L}nm {label} finite below barrier",ef<.2)
            check(f"{L}nm {label} infinite inverse mass",abs(ei*m-infinite_ground_ev(1,L))<1e-14)
            values[label]={"infinite_meV":ei*1000,"finite_meV":ef*1000}
        delta=values["QW_inferred"]["finite_meV"]-values["nominal_Gamma"]["finite_meV"]
        check(f"{L}nm empirical smaller mass gives higher level",delta>0)
        check(f"{L}nm quantum confinement shift modest",0<delta<5)
        checks[str(L)]=dict(values,finite_mass_selection_delta_meV=delta)
    check("finite well 5 nm > 8 nm",checks['5.0']['QW_inferred']['finite_meV']>checks['8.0']['QW_inferred']['finite_meV'])
    check("finite well 8 nm > 10 nm",checks['8.0']['QW_inferred']['finite_meV']>checks['10.0']['QW_inferred']['finite_meV'])
    for mass in (inferred,nominal):
        a=finite_ground_ev(mass,8,barrier_ev=.1)
        b=finite_ground_ev(mass,8,barrier_ev=.2)
        c=finite_ground_ev(mass,8,barrier_ev=.3)
        check(f"{mass} barrier monotonic",a<b<c)
        check(f"{mass} barrier upper limit",c<infinite_ground_ev(mass,8))
    try:finite_ground_ev(.7,0)
    except ValueError:check("negative dimension fail closed",True)
    else:raise AssertionError("invalid well width accepted")
    check("8nm finite offset about 1.087 meV",abs(checks['8.0']['finite_mass_selection_delta_meV']-1.087)<.002)
    return {"passed":len(tests),"all_passed":True,
            "source":"Molenkamp et al 1988 DOI 10.1103/PhysRevB.38.4314; Eppenga/Schuurmans Philips 44(5), 1988",
            "physical_model":"constant mass symmetric square QW with finite 0.2eV barriers and 0.9m0 barrier mass (chosen test parameters only)",
            "same_sample_experimental_fit":"OPEN",
            "optical_exciton_energy_fit":"OPEN",
            "369_unique_material_prediction":"OPEN",
            "cases":checks,"tests":tests}

if __name__=="__main__":
    print(json.dumps(run(),indent=2))
