#!/usr/bin/env python3
from __future__ import annotations

import random
import numpy as np


def term_values(x):
    pr=x[:9].reshape(3,3); pi=x[9:18].reshape(3,3)
    cr=x[18:27].reshape(3,3); ci=x[27:36].reshape(3,3)
    phi=pr+1j*pi; chi=cr+1j*ci
    A=phi.conj().T@phi; B=chi.conj().T@chi
    AL=phi@phi.conj().T; BL=chi@chi.conj().T
    nphi=float(np.real(np.trace(A))); nchi=float(np.real(np.trace(B)))
    return np.array([
        (nphi-1.0)**2,
        (nchi-1.0)**2,
        nphi*nphi-float(np.real(np.trace(A@A))),
        nchi*nchi-float(np.real(np.trace(B@B))),
        float(np.real(np.trace(A@B))),
        nphi*nchi-float(np.real(np.trace(AL@BL))),
    ])


def vacuum():
    x=np.zeros(36); x[7]=1.0; x[26]=1.0
    return x


def hessian_of_term(term_index, h=1e-4):
    x=vacuum(); n=36; H=np.zeros((n,n)); f0=term_values(x)[term_index]
    for i in range(n):
        ei=np.zeros(n); ei[i]=h
        H[i,i]=(term_values(x+ei)[term_index]-2*f0+term_values(x-ei)[term_index])/h**2
    for i in range(n):
        for j in range(i+1,n):
            ei=np.zeros(n); ej=np.zeros(n); ei[i]=h; ej[j]=h
            H[i,j]=H[j,i]=(
                term_values(x+ei+ej)[term_index]
                -term_values(x+ei-ej)[term_index]
                -term_values(x-ei+ej)[term_index]
                +term_values(x-ei-ej)[term_index]
            )/(4*h*h)
    return H


def expected_spectrum(coeff):
    a,b,c,d,e,f=coeff
    vals=[0]*12
    vals += [8*a]
    vals += [8*b]
    vals += [4*e]*2
    vals += [4*f]*4
    vals += [4*c+2*f]*4
    vals += [4*d+2*f]*4
    vals += [4*c+2*e+2*f]*4
    vals += [4*d+2*e+2*f]*4
    return sorted(float(v) for v in vals)


def verify():
    term_hessians=[hessian_of_term(k) for k in range(6)]
    # The six quadratic Hessians commute at the selected vacuum, so they admit
    # a common spectral decomposition there.
    max_commutator=0.0
    for i in range(6):
        for j in range(i+1,6):
            max_commutator=max(max_commutator,float(np.linalg.norm(
                term_hessians[i]@term_hessians[j]-term_hessians[j]@term_hessians[i]
            )))
    assert max_commutator < 1e-5

    rng=random.Random(20261016)
    replay_count=30
    for _ in range(replay_count):
        coeff=[rng.randint(1,5) for _ in range(6)]
        H=sum(coeff[k]*term_hessians[k] for k in range(6))
        got=sorted(float(v) for v in np.linalg.eigvalsh(H))
        exp=expected_spectrum(coeff)
        assert max(abs(x-y) for x,y in zip(got,exp)) < 1e-5

    return {
        "zero_mode_multiplicity": 12,
        "transverse_eigenvalue_families": {
            "8a": 1, "8b": 1, "4e": 2, "4f": 4,
            "4c+2f": 4, "4d+2f": 4,
            "4c+2e+2f": 4, "4d+2e+2f": 4,
        },
        "random_formula_replays": replay_count,
        "all_random_formula_replays_exact": True,
        "max_term_hessian_commutator_norm": max_commutator,
        "strict_stability_conditions": [
            "a>0", "b>0", "e>0", "f>0", "2c+f>0", "2d+f>0"
        ],
        "unique_physical_potential_derived": False,
    }


if __name__ == "__main__":
    for key,value in verify().items():
        print(f"{key}: {value}")
