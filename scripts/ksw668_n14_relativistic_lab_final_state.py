#!/usr/bin/env python3
"""C1: energy-dependent relativistic LAB kinematics of bare 14N(n,p)14C.

The input neutron kinetic energy is explicit and attributed; the default
0.0253-eV thermal example is NOT an observed individual neutron event.
Bare nuclei from NIST neutral isotopic masses corrected by NIST successive
ionization energies (DOI 10.18434/T4W30F), mp/me from 2022 CODATA.
The *real physical neutral target* would also have 7 bound/free electrons:
their correlations, recoil, electronic energy and gamma branching remain
separate source-measured experimental obligations.
"""
import argparse,json
from decimal import Decimal as D,getcontext
getcontext().prec=45
U=D("931.49410242")
ME=D("0.0005485799090441")
N14=(D("14.00307400443")-7*ME)*U+D("1486.0578277")/D(1000000)
C14=(D("14.0032419884")-6*ME)*U+D("1030.10849879")/D(1000000)
NEUTRON=D("1.00866491595")*U
PROTON=D("1.0072764665789")*U

def solve(incident_neutron_kinetic_eV,source):
    if not source or not source.strip():raise ValueError("Original incident energy provenance required")
    T=D(str(incident_neutron_kinetic_eV))/D(1000000)
    if T<0:raise ValueError("Negative neutron kinetic energy")
    En=NEUTRON+T
    pn=(T*(2*NEUTRON+T)).sqrt()
    s=N14*N14+NEUTRON*NEUTRON+2*N14*En
    W=s.sqrt()
    ep=(s+PROTON*PROTON-C14*C14)/(2*W)
    ec=(s+C14*C14-PROTON*PROTON)/(2*W)
    kallen=(s-(PROTON+C14)*(PROTON+C14))*(s-(PROTON-C14)*(PROTON-C14))
    if kallen<0:raise ValueError("Original selected nuclear channel below threshold")
    pstar=kallen.sqrt()/(2*W)
    beta=pn/(N14+En)
    gamma=(N14+En)/W
    assert abs(ep+ec-W)<D("1e-37")
    angles=[]
    for cosine in (D("-1"),D("0"),D("1")):
        Ep=gamma*(ep+beta*pstar*cosine)
        Ec=gamma*(ec-beta*pstar*cosine)
        ppz=gamma*(pstar*cosine+beta*ep)
        pcz=gamma*(-pstar*cosine+beta*ec)
        pt=pstar*(1-cosine*cosine).sqrt()
        assert abs(Ep+Ec-(N14+En))<D("1e-36")
        assert abs(ppz+pcz-pn)<D("1e-36")
        assert abs(Ep*Ep-ppz*ppz-pt*pt-PROTON*PROTON)<D("1e-32")
        assert abs(Ec*Ec-pcz*pcz-pt*pt-C14*C14)<D("1e-32")
        angles.append({"cos_theta_COM":str(cosine),
            "proton_kinetic_lab_MeV":str(Ep-PROTON),
            "carbon14_kinetic_lab_MeV":str(Ec-C14),
            "proton_pz_MeV_c":str(ppz),
            "carbon14_pz_MeV_c":str(pcz),
            "opposed_transverse_p_MeV_c":str(pt),
            "energy_momentum_and_two_mass_shells":"PASS"})
    return {"status":"PASS: exact source-based Decimal bare-nucleus lab kinematics",
       "original_source_DOI":"10.18434/T4W30F",
       "incident_energy_source":source,
       "input_neutron_kinetic_eV":str(incident_neutron_kinetic_eV),
       "initial_state":"14N7+ bare ground nucleus at rest, plus incoming neutron",
       "final_state":"14C6+ bare ground nucleus and free proton",
       "nuclear_Q_MeV":str(N14+NEUTRON-C14-PROTON),
       "initial_lab_neutron_momentum_MeV_c":str(pn),
       "total_COM_energy_MeV":str(W),
       "two_body_final_COM_momentum_MeV_c":str(pstar),
       "COM_beta":str(beta),"COM_gamma":str(gamma),
       "three_original_COM_angle_benchmarks":angles,
       "electron_photon_excitation_branching_verified":False,
       "original_measured_neutron_event":False}

if __name__=="__main__":
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--neutron-energy-eV",default="0.0253")
    ap.add_argument("--source",default="standard illustrative 0.0253-eV thermal neutron; NOT measured event")
    args=ap.parse_args()
    print(json.dumps(solve(args.neutron_energy_eV,args.source),indent=2))
