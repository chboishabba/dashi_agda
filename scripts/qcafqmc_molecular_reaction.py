#!/usr/bin/env python3
"""Finite electronic Hamiltonian regression and actual-integral reaction cut.

The results are source-conditioned. No fictitious nickel geometry, integral
tensor, geometry offset, nuclear energy or trial state is generated.
"""
import argparse
import json
import numpy as np
from qcafqmc_molecular_fcidump import (fci_matrix,parse_fcidump,
                                        slater_amplitudes,hubbard_fixture)

HARTREE_TO_KCAL_MOL=627.5094740631

def regression():
    h,eri,na,nb,core=hubbard_fixture()
    H,states=fci_matrix(h,eri,na,nb,core)
    assert len(states)==4
    assert np.isclose(np.linalg.eigvalsh(H)[0],2-2*np.sqrt(2),atol=1e-12)
    trial=np.ones((2,1))/np.sqrt(2)
    amps=slater_amplitudes(trial,trial,states)
    assert np.allclose(amps,np.ones(4)/2)
    assert np.isclose(np.vdot(amps,amps),1)
    h0=np.zeros((1,1));eri0=np.zeros((1,1,1,1));eri0[0,0,0,0]=.8
    h0[0,0]=-1.2
    e0,_=fci_matrix(h0,eri0,1,1,.3)
    assert np.isclose(e0[0,0],-2.4+.8+.3)
    return {"hubbard_ground_energy":float(np.linalg.eigvalsh(H)[0]),
            "slater_norm":float(np.vdot(amps,amps).real),
            "single_orbital_two_electron_energy":float(e0[0,0]),
            "tests_passed":True}

def state_energy(path,max_dimension=700):
    h,eri,na,nb,core=parse_fcidump(path)
    from math import comb
    dimension=comb(len(h),na)*comb(len(h),nb)
    if dimension>max_dimension:
        raise ValueError(f"FCI dimension {dimension} exceeds safe cap {max_dimension}; use scalable AFQMC")
    H,_=fci_matrix(h,eri,na,nb,core)
    return float(np.linalg.eigvalsh(H)[0])

def reaction(before,after,max_dimension=700):
    energy_before=state_energy(before,max_dimension)
    energy_after=state_energy(after,max_dimension)
    return {"scope":"source-specific small-FCI comparator, not IonQ original nickel AFQMC",
            "reactant_fcidump":before,"product_fcidump":after,
            "reactant_ground_hartree":energy_before,
            "product_ground_hartree":energy_after,
            "delta_e_hartree":energy_after-energy_before,
            "delta_e_kcal_mol":(energy_after-energy_before)*HARTREE_TO_KCAL_MOL,
            "not_included":"zero-point vibrational, thermal corrections and any unspecified system terms"}
if __name__=="__main__":
    p=argparse.ArgumentParser()
    p.add_argument("--before")
    p.add_argument("--after")
    p.add_argument("--max-dimension",type=int,default=700)
    a=p.parse_args()
    if (a.before is None)!=(a.after is None):
        p.error("--before and --after required together")
    print(json.dumps(reaction(a.before,a.after,a.max_dimension)
                     if a.before else regression(),indent=2))
