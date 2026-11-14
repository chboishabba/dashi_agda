#!/usr/bin/env python3
"""Exact Fourier-parity audit of the proposed R823 helical shear shortcut.

The attachment's u_bad has div(u_bad) = (K-1)*eps*sin(x)*sin(K*z).
It is not divergence-free for K>1 and eps != 0.
For corrected u_z = -(eps/K)*sin(x)*cos(K*z), div(u_fix)=0.
Every Fourier mode of u_fix has vertical frequency +-K; three
such frequencies never add to zero. The unforced incompressible
Navier-Stokes cubic H1 transfer integral vanishes.

With normalized T^3 spatial mean, E=||u||_2^2,
G=||grad u||_2^2, H=||Delta u||_2^2, and
Phi=E+c*ln(1+G), initial dPhi/dt=-2nu(G+cH/(1+G))<0,
for nu>0, c>=0. This is NOT an original R823 source theorem.
"""
from fractions import Fraction as Q
import json

def case(K: int, eps: Q, nu: Q, c: Q):
    assert K >= 1 and nu > 0 and c >= 0
    k, e2 = Q(K), eps*eps
    original_divergence_sine_coefficient = eps*(K-1)
    corrected_divergence_sine_coefficient = -eps+(eps/k)*k
    assert corrected_divergence_sine_coefficient == 0
    E = 1 + (e2/4)*(1+1/(k*k))
    G = k*k + (e2/4)*(k*k+2+1/(k*k))
    H = k**4 + (e2/4)*(k*k+1)**2*(1+1/(k*k))
    assert E>0 and G>0 and H>0
    zero_mode_triples = [(a,b,d) for a in (-K,K) for b in (-K,K)
                         for d in (-K,K) if a+b+d == 0]
    assert zero_mode_triples == []
    nonlinear_enstrophy_transfer = Q(0)
    dE = -2*nu*G
    dG = -2*nu*H + nonlinear_enstrophy_transfer
    dPhi = dE+c*dG/(1+G)
    assert dE<0 and dG<0 and dPhi<0
    return {"K":K,"epsilon":str(eps),"nu":str(nu),"c":str(c),
            "original_divergence_coefficient":str(original_divergence_sine_coefficient),
            "corrected_divergence_coefficient":str(corrected_divergence_sine_coefficient),
            "energy_mean":str(E),"gradient_energy_mean":str(G),
            "laplacian_energy_mean":str(H),
            "nonlinear_transfer_zero_from_vertical_fourier_parity":True,
            "dPhi_dt":str(dPhi),"dPhi_dt_strictly_negative":True}

def check():
    tests=[case(K,e,Q(1,2),c) for K in (1,2,3,4,8,31)
        for e in (Q(0),Q(1,9),Q(1),Q(7,3))
        for c in (Q(0),Q(1,2),Q(8))]
    assert case(2,Q(1),Q(1),Q(1))["original_divergence_coefficient"] == "1"
    return {"schema":"ns-r823-shear-source-negative-control-v1",
            "result":"PASS","exact_rational_tests":len(tests),
            "K2_original_divergence_coefficient":"1",
            "divergence_free_correction":"u_z=-(eps/K)sin(x)cos(Kz)",
            "all_corrected_initial_reserve_derivatives_negative":True,
            "example":case(2,Q(1),Q(1),Q(1)),
            "original_R823_source_reserve_weld":False,
            "original_Galerkin_rate_R853_weld":False,
            "kernel_receipt":False}
if __name__ == "__main__":
    print(json.dumps(check(),indent=2))
