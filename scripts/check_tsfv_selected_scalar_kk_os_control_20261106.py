#!/usr/bin/env python3
"""S01-S09 scoped analytic reference, NOT original physical TSVF/YM.

Chosen source: positive-mass 3D nearest-neighbour scalar lattice probed by
a local linear-response instrument. Its continuum acoustic 3+1 metric is
used as the SAME g4 in a flat Einstein-vacuum five-dimensional KK lift.
Its free Gaussian quantum Fock/OS comparison is physically noncollapsed,
but deliberately does NOT instantiate the nontrivial interacting 4D
Yang-Mills source, the 2017 real TSVF pointer, or the Clay endpoint.

The code checks exact symbolic finite algebra and selected numerical
spectral/OS probes. Analytic Hilbert/Stone/reflection-positivity theorems
have independent mathematical sources and are NOT proved by this script.
"""
import json
from itertools import product
from pathlib import Path

import numpy as np
import sympy as sp


def selected_lattice_wave():
    a, c, mu, w = sp.symbols("a c mu omega", real=True)
    ks = sp.symbols("kx ky kz", real=True)
    omega_sq = mu**2 + 4*c**2 / a**2 * sum(
        sp.sin(a*k/2)**2 for k in ks)
    series = sp.expand(sp.series(omega_sq, a, 0, 4).removeO())
    target = mu**2 + c**2*sum(k*k for k in ks) - c**2*a**2*sum(k**4 for k in ks)/12
    assert sp.simplify(series - target) == 0
    # Independent source-selected operational dispersion, not a
    # hand-inserted Lorentzian signature fixture.
    principal = sum(k*k for k in ks) - w*w/c**2
    ginv = sp.diag(-1/c**2, 1, 1, 1)
    p = sp.Matrix([w, *ks])
    assert sp.simplify((p.T*ginv*p)[0] - principal) == 0
    assert sp.simplify(ginv.det()+1/c**2) == 0
    for k in ks:
        assert sp.simplify(sp.diff(principal, k, 2)/2-1) == 0
    assert sp.simplify(sp.diff(principal, w, 2)/2+1/c**2) == 0
    return {
        "chosen_microscopic_source":"three spatial nearest-neighbour oscillator lattice, mass mu>0",
        "observer":"local kick J_n(t), retarded field response q_n(t)",
        "discrete_dispersion":str(omega_sq),
        "continuum_principal":str(principal),
        "leading_lattice_error":str(-c**2*a**2*sum(k**4 for k in ks)/12),
        "caveat":"three spatial axes CHOSEN in the source; retarded continuum propagation theorem not Agda-proved"
    }


def selected_kk_flat_vacuum():
    coords = sp.symbols("t x y z chi")
    c = sp.Rational(3, 2)
    radius = sp.Rational(5, 3)
    A = sp.Matrix([sp.Rational(1,5), -sp.Rational(2,7),
                   sp.Integer(0), sp.Rational(1,11)])
    g4 = sp.diag(-c*c, 1, 1, 1)
    ginv = sp.diag(-1/(c*c), 1, 1, 1)
    G = sp.zeros(5)
    for i in range(4):
        for j in range(4):
            G[i,j] = g4[i,j] + radius**2*A[i]*A[j]
        G[i,4] = radius**2*A[i]
        G[4,i] = radius**2*A[i]
    G[4,4] = radius**2
    assert sp.simplify(G.det()+c*c*radius**2)==0
    assert sp.simplify(G[:4,:4] - G[:4,4]*G[4,:4]/G[4,4]-g4)==sp.zeros(4)
    assert sp.simplify(G*G.inv()-sp.eye(5))==sp.zeros(5)
    inv_expected=sp.zeros(5)
    for i in range(4):
        for j in range(4):
            inv_expected[i,j]=ginv[i,j]
        inv_expected[i,4]=-(ginv*A)[i]
        inv_expected[4,i]=inv_expected[i,4]
    inv_expected[4,4]=1/(radius**2)+(A.T*ginv*A)[0]
    assert sp.simplify(G.inv()-inv_expected)==sp.zeros(5)
    # Constant global chart coefficients give zero Levi-Civita
    # derivatives, connection, curvature and Einstein tensor.
    assert all(sp.diff(G[i,j],x)==0 for i,j,x in product(range(5),range(5),coords))
    assert all(sp.diff(A[i],coords[j])-sp.diff(A[j],coords[i])==0
               for i,j in product(range(4),range(4)))
    p=sp.Matrix(sp.symbols("omega kx ky kz"))
    assert sp.simplify((p.T*ginv*p)[0]+p[0]**2/c**2-
                       sum(p[i]**2 for i in range(1,4)))==0
    return {
        "chosen_manifold":"R_t x R^3 x S1",
        "g4":str(g4),
        "KK_A":str(list(A)),
        "circle_radius":str(radius),
        "G5":str(G),
        "det_G5":str(G.det()),
        "ricci_5D":"0 exactly (constant Levi-Civita coefficients)",
        "einstein_5D":"0 exactly (vacuum T_AB = 0)",
        "horizontal_reduction_equals_source_metric":True,
        "caveat":"flat vacuum, flat connection; NO interacting matter/TSVF/YM identity"
    }


def free_fock_os():
    # Real selfadjoint H on infinite-dimensional bosonic occupation
    # Hilbert l2(N^3): diagonal multiplication with nonnegative energy.
    # The finite-support vectors below are merely a test of a dense
    # invariant core; analytic essential selfadjointness is external.
    hbar=sp.Rational(7,5)
    c=sp.Rational(3,2)
    mu=sp.Rational(5,4)
    omegas=[mu,sp.sqrt(mu**2+c**2),sp.sqrt(mu**2+2*c**2)]
    ts=[sp.Rational(1,6),sp.Rational(1,3),
        sp.Rational(2,5),sp.Rational(3,4)]
    for om in omegas:
        v=sp.Matrix([sp.exp(-om*t) for t in ts])
        K=(v*v.T)*hbar/(2*om)
        for coeffs in ((1,0,0,0),(0,1,-1,2),(2,-3,4,-1)):
            coeff=sp.Matrix(coeffs)
            assert float(sp.N((coeff.T*K*coeff)[0]))>=-1e-12
        assert K==v*v.T*hbar/(2*om)
    modes=np.array([float(sp.N(x)) for x in omegas])
    labels=list(product(range(5),repeat=3))
    energies=np.array([float(hbar)*np.dot(modes,n) for n in labels])
    # Actual positive gap in the chosen FREE three-mode Fock model:
    # min_{n!=0} E_n = hbar*mu = 7/4. This is NOT Clay YM.
    free_gap=hbar*mu
    assert free_gap==sp.Rational(7,4)
    assert all(E==0 or E>=float(free_gap)-1e-12 for E in energies)
    rng=np.random.default_rng(404)
    psi=rng.normal(size=len(labels))+1j*rng.normal(size=len(labels))
    psi=psi/np.linalg.norm(psi)
    t=0.61;tau=0.33
    U=np.exp(-1j*t*energies/float(hbar))
    T=np.exp(-tau*energies/float(hbar))
    assert abs(np.linalg.norm(U*psi)-1)<1e-12
    assert np.linalg.norm(T*psi)<=1+1e-12
    P=(energies<=2).astype(float)
    assert np.allclose(P*P,P)
    assert np.allclose(P*(U*psi),U*(P*psi))
    z=tau+1j*t
    assert abs(np.vdot(psi,np.exp(-z*energies/float(hbar))*psi)-
               np.vdot(psi,T*U*psi))<1e-12
    return {
        "Hilbert":"noncollapsed infinite bosonic Fock l2(N^3) occupation space",
        "Hamiltonian":"H|n>=hbar*(sum_i omega_i n_i)|n>, domain weighted ell2",
        "spectral_projections":"energy-indicator multiplication operators",
        "free_gap_energy":str(free_gap),
        "free_gap_scope":"FREE Gaussian oscillator, not non-Abelian interacting YM",
        "real_time":"U(t)=exp(-itH/hbar)",
        "euclidean_time":"T(tau)=exp(-tau H/hbar)",
        "Gaussian_OS_two_point":"C_i(tau)=hbar*exp(-omega_i*abs(tau))/(2omega_i)",
        "spectral_and_wick_samples":"PASS on 125-state dense-core truncation",
        "caveat":"full OS reconstruction uses external Gaussian Wick/Fock theorem; NOT original Yang-Mills OS source"
    }


if __name__=="__main__":
    receipt={
        "S01_S04":selected_lattice_wave(),
        "S05_S06":selected_kk_flat_vacuum(),
        "S08_S09":free_fock_os(),
        "S11":{
            "Agda_kernel":"NOT CHECKED BY THIS SCRIPT",
            "original_TSVF_source":"UNINHABITED",
            "interacting_YM_OS":"OTHER WORKER/OPEN",
            "same_physical_source_as_original":"NO",
            "scope":"constructed free scalar / flat KK consistency control"
        }
    }
    print(json.dumps(receipt,indent=2))
    print("PASS: scoped symbolic 3+1 wave, 5D Einstein vacuum and noncollapsed free-field/OS controls")
