#!/usr/bin/env python3
"""Actual original a=t AdS5 ell=0,2,4 FULL finite-volume C3 check.

Unlike the r² local witness, this includes the entire homogeneous radial
Dirichlet finite-volume generator and each dimension's DISTINCT radial
volume norm. Normalize each channel by sqrt(V_q), so C3 label cycling is
genuinely unitary on the common direct-sum Hilbert space. Test its full
matrix commutator and modal eigenvalue spectra; both refute the natural
physical C3 intertwiner. No assertion about every possible nonlocal map.
"""
import json
import numpy as np
from ksw668_f8_full_coupled_weighted_sbp_energy import radial_stiffness
DIMS=(3,7,11)

def normalized_radial(d,nr,dr):
    if nr<5 or dr<=0:raise ValueError('finite radial grid')
    L,V=radial_stiffness(d,nr,dr)
    L=L[:-1,:-1];V=V[:-1]  # original outer radial Dirichlet cell
    S=np.sqrt(V)[:,None]*L/np.sqrt(V)[None,:]
    assert np.allclose(S,S.T,rtol=1e-11,atol=1e-9)
    return S,V,L

def audit(nr=12,dr=.015):
    if nr<5 or dr<=0:raise ValueError('grid')
    mods=[normalized_radial(d,nr,dr) for d in DIMS]
    n=nr-1
    T=np.kron(np.roll(np.eye(3),1,axis=0),np.eye(n))
    A=np.zeros((3*n,3*n))
    for q,(S,V,L) in enumerate(mods):
        A[q*n:(q+1)*n,q*n:(q+1)*n]=S
    assert np.array_equal(T.T@T,np.eye(3*n))
    assert np.array_equal(np.linalg.matrix_power(T,3),np.eye(3*n))
    C=A@T-T@A
    assert np.allclose(C[n:2*n,0:n],mods[1][0]-mods[0][0])
    eig=[np.linalg.eigvalsh(x[0]) for x in mods]
    gaps=[float(np.max(np.abs(eig[q]-eig[0]))) for q in (1,2)]
    rng=np.random.default_rng(391);z=rng.normal(size=3*n)
    assert abs(np.linalg.norm(T@z)-np.linalg.norm(z))<1e-12
    assert np.linalg.norm(C@z)>1e-3 and all(g>0 for g in gaps)
    return dict(nr_total=nr,dr=dr,dimensions=DIMS,
        compensated_C3_is_unitary=True,compensated_C3_cube_is_identity=True,
        full_operator_C3_commutator_Frobenius=float(np.linalg.norm(C)),
        eigenvalue_gaps_vs_ell0=gaps,
        radial_channel_C3_is_physical_symmetry=False,
        arbitrary_nonlocal_intertwiners_all_disproved=False)
if __name__=='__main__':print(json.dumps(audit(),indent=2))
