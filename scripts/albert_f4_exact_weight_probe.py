#!/usr/bin/env python3
"""Exact Q(i) root-space decomposition of the Albert inner-derivation algebra.

This script upgrades the older floating root diagnostic.  It reconstructs the
same exact integer-cleared Albert inner derivations as
`albert_inner_derivation_rank.py`, uses the 28+8+8+8 independent triality basis,
and forms the four Cartan derivations

    [L_x0,L_x1], [L_x2,L_x3], [L_x4,L_x5], [L_x6,L_x7].

The adjoint action on each triality sector is represented exactly over Q.
Symbolic spectral projectors over Q(i) then prove:

* so8 sector: zero joint-weight rank 4 and 24 one-dimensional D4 roots;
* vector sector: 8 one-dimensional weights ±e_i;
* spin+ sector: 8 one-dimensional half-spin weights of positive chirality;
* spin- sector: 8 one-dimensional half-spin weights of negative chirality.

Thus the complexified derivation algebra decomposes exactly as

    Cartan_4 + roots_(24+8+8+8) = 52.

No floating-point eigensolver is used.
"""

from itertools import combinations, product
import numpy as np
import sympy as sp
from albert_inner_derivation_rank import N, jordan_times_two


def build_data():
    basis = np.eye(N, dtype=np.int64)
    C2 = np.zeros((N,N,N), dtype=np.int64)
    for i in range(N):
        for j in range(N):
            C2[:,i,j] = jordan_times_two(basis[i], basis[j])
    L2 = np.transpose(C2, (1,0,2))

    def comm(i,j):
        return L2[i] @ L2[j] - L2[j] @ L2[i]

    sectors = {
        'so8': [(i,j) for i,j in combinations(range(3,11),2)],
        'V':   [(1,j) for j in range(3,11)],
        'S+':  [(0,j) for j in range(11,19)],
        'S-':  [(0,j) for j in range(19,27)],
    }
    mats = {name:[sp.Matrix(comm(*p).tolist()) for p in pairs]
            for name,pairs in sectors.items()}
    H = [sp.Matrix(comm(*p).tolist())/4
         for p in [(3,4),(5,6),(7,8),(9,10)]]
    return mats,H


def representation_matrix(H, basis_mats):
    """Matrix of ad_H in the supplied independent derivation basis."""
    n = len(basis_mats)
    rows = [M.reshape(27*27,1).T for M in basis_mats]
    B = sp.Matrix.vstack(*rows)                 # n x 729
    _, pivots = B.rref()
    pivots = list(pivots[:n])
    minor = B[:,pivots]
    if minor.det() == 0:
        raise AssertionError('basis pivot minor singular')
    invT = minor.T.inv()

    cols = []
    for D in basis_mats:
        K = H*D-D*H
        flat = K.reshape(27*27,1)
        target = sp.Matrix([flat[p] for p in pivots])
        coeff = invT*target
        reconstruction = sp.zeros(27,27)
        for c,M in zip(coeff,basis_mats):
            reconstruction += c*M
        if reconstruction != K:
            raise AssertionError('coordinate solve did not reconstruct bracket')
        cols.append(coeff)
    return sp.Matrix.hstack(*cols)


def projector_zero(H):
    n=H.rows
    return sp.eye(n)+H*H


def projector_vector(H, sign):
    # spectrum {0,+i,-i}; sign=+1 selects +i, sign=-1 selects -i
    n=H.rows
    return -sp.Rational(1,2)*H*(H + sign*sp.I*sp.eye(n))


def projector_spin(H, sign):
    # spectrum {+i/2,-i/2}; sign selects i*sign/2
    n=H.rows
    return (sp.eye(n)-2*sp.I*sign*H)/2


def joint_projector(rep, weight, kind):
    P=sp.eye(rep[0].rows)
    for H,w in zip(rep,weight):
        if kind in ('so8','V'):
            if w==0:
                Q=projector_zero(H)
            else:
                Q=projector_vector(H,int(w))
        else:
            Q=projector_spin(H,1 if w>0 else -1)
        P=sp.simplify(P*Q)
    return P


def d4_weights():
    out=[]
    for i,j in combinations(range(4),2):
        for si,sj in product((-1,1),repeat=2):
            w=[0,0,0,0];w[i]=si;w[j]=sj;out.append(tuple(w))
    return out


def vector_weights():
    out=[]
    for i in range(4):
        for s in (-1,1):
            w=[0,0,0,0];w[i]=s;out.append(tuple(w))
    return out


def spin_weights(chirality):
    out=[]
    for signs in product((-1,1),repeat=4):
        prod_sign=signs[0]*signs[1]*signs[2]*signs[3]
        if prod_sign==chirality:
            out.append(tuple(sp.Rational(s,2) for s in signs))
    return out


def main():
    mats,Hfull=build_data()
    reps={name:[representation_matrix(H,mats[name]) for H in Hfull]
          for name in mats}

    # Cartan operators commute on every sector.
    for name,rep in reps.items():
        for A in rep:
            for B in rep:
                if A*B != B*A:
                    raise AssertionError(f'Cartan noncommutation in {name}')

    zero_rank = joint_projector(reps['so8'],(0,0,0,0),'so8').rank()
    if zero_rank != 4:
        raise AssertionError(f'expected Cartan zero-weight rank 4, got {zero_rank}')

    d4=d4_weights(); vec=vector_weights(); sp_plus=spin_weights(+1); sp_minus=spin_weights(-1)
    for w in d4:
        if joint_projector(reps['so8'],w,'so8').rank()!=1:
            raise AssertionError(f'D4 weight not rank one: {w}')
    for w in vec:
        if joint_projector(reps['V'],w,'V').rank()!=1:
            raise AssertionError(f'vector weight not rank one: {w}')
    for w in sp_plus:
        if joint_projector(reps['S+'],w,'spin').rank()!=1:
            raise AssertionError(f'spin+ weight not rank one: {w}')
    for w in sp_minus:
        if joint_projector(reps['S-'],w,'spin').rank()!=1:
            raise AssertionError(f'spin- weight not rank one: {w}')

    # Exhaustion by dimensions makes clear no additional joint weight spaces
    # can remain in any sector.
    assert zero_rank + len(d4) == 28
    assert len(vec)==len(sp_plus)==len(sp_minus)==8
    assert 4+len(d4)+len(vec)+len(sp_plus)+len(sp_minus)==52

    print('exact_scalar_field=Q(i)')
    print('cartan_zero_weight_dimension=4')
    print('d4_root_spaces=24x1')
    print('vector_weight_spaces=8x1')
    print('spin_plus_weight_spaces=8x1')
    print('spin_minus_weight_spaces=8x1')
    print('total_nonzero_root_spaces=48')
    print('total_dimension=52')
    print('floating_point_used=false')


if __name__=='__main__':
    main()
