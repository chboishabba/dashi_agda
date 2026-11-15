#!/usr/bin/env python3
"""Original FCIDUMP → ipie modified-Cholesky Hamiltonian identity guard.

The input one-/two-electron integrals and constant Ecore must match those
actually consumed by AFQMC. In the molecular chemists' convention the
Cholesky factors satisfy (pq|rs)=sum_gamma L[p,q,gamma] L[r,s,gamma].

Attribution: ipie modified-Cholesky FCIDUMP converter and molecular
integral definitions; original DASHI qcafqmc_molecular_fcidump.py.
This checks a *numerical approximation tolerance*, not a proof that
an unrelated molecular orbital frame is the published IonQ frame.
"""
import argparse
import json
import numpy as np
from qcafqmc_molecular_fcidump import parse_fcidump

class HamiltonianMismatch(ValueError):
    pass

def check_arrays(h1,eri,ecore,ham_h1,chol,ham_ecore,
                 max_relative_eri_error=5e-5,
                 max_absolute_h1_error=1e-8,
                 max_absolute_core_error=1e-8):
    h1=np.asarray(h1,dtype=np.complex128)
    eri=np.asarray(eri,dtype=np.complex128)
    n=h1.shape[0]
    if h1.shape!=(n,n) or eri.shape!=(n,n,n,n):
        raise HamiltonianMismatch("bad source FCIDUMP tensor dimensions")
    h1_ipie=np.asarray(ham_h1,dtype=np.complex128)
    if h1_ipie.ndim==3:
        if h1_ipie.shape!=(2,n,n):
            raise HamiltonianMismatch("unexpected iPie spin-resolved one-body tensor")
        if not np.allclose(h1_ipie[0],h1_ipie[1],atol=max_absolute_h1_error):
            raise HamiltonianMismatch("RHF-equivalent spatial Hamiltonian has spin split")
        h1_ipie=h1_ipie[0]
    if h1_ipie.shape!=(n,n):
        raise HamiltonianMismatch("iPie one-body tensor shape")
    chol=np.asarray(chol)
    if chol.ndim!=2 or chol.shape[0]!=n*n:
        raise HamiltonianMismatch("iPie Cholesky tensor shape")
    if not np.isfinite(chol).all():
        raise HamiltonianMismatch("nonfinite Cholesky factors")
    # For the current real-valued STO-3G/S0 case the reconstructed
    # two-body tensor must be in the same (p,q,r,s) spatial ordering.
    reconstructed=chol@chol.T
    original=eri.reshape(n*n,n*n)
    error=float(np.linalg.norm(reconstructed-original))
    denom=max(float(np.linalg.norm(original)),1e-15)
    rel=error/denom
    h1_error=float(np.max(abs(h1_ipie-h1)))
    core_error=float(abs(complex(ham_ecore)-ecore))
    if not np.isfinite(rel) or rel>max_relative_eri_error:
        raise HamiltonianMismatch(f"Cholesky two-electron source mismatch: {rel}")
    if h1_error>max_absolute_h1_error or core_error>max_absolute_core_error:
        raise HamiltonianMismatch(
            f"one-body or core mismatch: {h1_error}, {core_error}")
    return {"spatial_orbitals":n,"cholesky_vectors":chol.shape[1],
            "ERI_relative_frobenius_error":rel,
            "one_electron_max_abs_error":h1_error,
            "effective_core_abs_error":core_error,
            "same_source_integral_conventions_admitted":True}

def check_ipie_hamiltonian(fcidump,ham,threshold=5e-5):
    h1,eri,na,nb,ecore=parse_fcidump(fcidump)
    if na!=nb or h1.shape[0]!=8:
        raise HamiltonianMismatch("selected closed-shell 8-orbital chemistry expected")
    return check_arrays(h1,eri,ecore,ham.H1,ham.chol,ham.ecore,
                        max_relative_eri_error=threshold)

def self_test():
    rng=np.random.default_rng(42)
    n=3
    chol=rng.normal(size=(n*n,5))
    # A physical real-valued ERI has symmetric pair factors.
    chol=chol.reshape(n,n,5)
    chol=.5*(chol+chol.transpose(1,0,2))
    chol=chol.reshape(n*n,5)
    eri=(chol@chol.T).reshape((n,n,n,n))
    h=rng.normal(size=(n,n));h=.5*(h+h.T)
    passing=check_arrays(h,eri,1.2,np.stack((h,h)),chol,1.2)
    wrong=chol.copy();wrong[0,0]+=.1
    try:check_arrays(h,eri,1.2,np.stack((h,h)),wrong,1.2)
    except HamiltonianMismatch:wrong_rejected=True
    else:raise AssertionError("altered two-body Cholesky accepted")
    try:check_arrays(h,eri,1.2,np.stack((h,h)),chol,1.3)
    except HamiltonianMismatch:core_rejected=True
    else:raise AssertionError("altered core energy accepted")
    return {"positive":passing,"altered_two_electron_rejected":wrong_rejected,
            "altered_core_energy_rejected":core_rejected,
            "ipie_runtime_executed":False}
if __name__=="__main__":
    parser=argparse.ArgumentParser()
    parser.add_argument("--self-test",action="store_true")
    a=parser.parse_args()
    if not a.self_test:parser.error("use --self-test")
    print(json.dumps(self_test(),indent=2))
