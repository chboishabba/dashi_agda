#!/usr/bin/env python3
"""Exact inner-derivation audit for the rational Albert coordinate algebra.

This mirrors the coordinate convention in
DASHI/Mathematics/Algebra/RationalAlbertJordanProductExact.agda.

All structure constants are stored after multiplication by 2, so they are
integers.  If L_i is left Jordan multiplication by coordinate basis vector e_i,
then 4[L_i,L_j] is an integer 27x27 matrix.  We compute all nonzero such
commutators, verify the derivation law exactly on all coordinate basis pairs,
and compute their exact Q-rank using SymPy's integer DomainMatrix backend.
"""

from itertools import combinations
import numpy as np
import sympy as sp

N = 27


def qmul(a, b):
    a0,a1,a2,a3 = map(int, a)
    b0,b1,b2,b3 = map(int, b)
    return np.array([
        a0*b0-a1*b1-a2*b2-a3*b3,
        a0*b1+a1*b0+a2*b3-a3*b2,
        a0*b2-a1*b3+a2*b0+a3*b1,
        a0*b3+a1*b2-a2*b1+a3*b0,
    ], dtype=np.int64)


def qconj(a):
    a = np.asarray(a, dtype=np.int64)
    return np.array([a[0],-a[1],-a[2],-a[3]], dtype=np.int64)


def omul(a, b):
    a = np.asarray(a, dtype=np.int64)
    b = np.asarray(b, dtype=np.int64)
    A,B = a[:4],a[4:]
    C,D = b[:4],b[4:]
    return np.concatenate([
        qmul(A,C)-qmul(qconj(D),B),
        qmul(D,A)+qmul(B,qconj(C)),
    ])


def oconj(a):
    a = np.asarray(a, dtype=np.int64)
    return np.concatenate([[a[0]],-a[1:]])


def inner(a, b):
    return int(omul(a, oconj(b))[0])


def jordan_times_two(v, w):
    """Return 2*(v o w), with exact integer coordinates."""
    a,b,c = v[:3]
    x,y,z = v[3:11],v[11:19],v[19:27]
    A,B,C = w[:3]
    X,Y,Z = w[3:11],w[11:19],w[19:27]

    d0 = 2*(a*A + inner(z,Z) + inner(y,Y))
    d1 = 2*(b*B + inner(z,Z) + inner(x,X))
    d2 = 2*(c*C + inner(y,Y) + inner(x,X))

    def total(terms):
        out = np.zeros(8, dtype=np.int64)
        for t in terms:
            out += t
        return out

    ox = total([
        omul(oconj(z),oconj(Y)), b*X, C*x,
        omul(oconj(Z),oconj(y)), B*x, c*X,
    ])
    oy = total([
        A*y, omul(oconj(x),oconj(Z)), c*Y,
        a*Y, omul(oconj(X),oconj(z)), C*y,
    ])
    oz = total([
        a*Z, B*z, omul(oconj(y),oconj(X)),
        A*z, b*Z, omul(oconj(Y),oconj(x)),
    ])
    return np.concatenate([[d0,d1,d2],ox,oy,oz])


def main():
    basis = np.eye(N, dtype=np.int64)
    C2 = np.zeros((N,N,N), dtype=np.int64)
    for i in range(N):
        for j in range(N):
            C2[:,i,j] = jordan_times_two(basis[i], basis[j])

    # L2[i] = 2*L_{e_i}; hence N_ij below equals 4[L_i,L_j].
    L2 = np.transpose(C2, (1,0,2))
    commutators = []
    pairs = []
    for i,j in combinations(range(N),2):
        Dij = L2[i] @ L2[j] - L2[j] @ L2[i]
        if np.any(Dij):
            commutators.append(Dij)
            pairs.append((i,j))

    # Exact derivation identity after clearing common denominator 8:
    # D C(x,y) = C(Dx,y) + C(x,Dy).
    for pair,D in zip(pairs,commutators):
        lhs = np.einsum('ka,aij->kij',D,C2,dtype=np.int64)
        rhs1 = np.einsum('ai,kaj->kij',D,C2,dtype=np.int64)
        rhs2 = np.einsum('aj,kia->kij',D,C2,dtype=np.int64)
        if not np.array_equal(lhs, rhs1 + rhs2):
            raise AssertionError(f'derivation law failed for pair {pair}')

    rows = [[int(x) for x in D.reshape(-1)] for D in commutators]
    rank = sp.polys.matrices.DomainMatrix.from_list(rows, sp.ZZ).rank()

    print(f'coordinate_dimension={N}')
    print(f'basis_products_checked={N*N}')
    print(f'nonzero_inner_commutators={len(commutators)}')
    print('all_inner_commutators_derivations=true')
    print(f'exact_rational_span_rank={rank}')

    assert len(commutators) == 324
    assert rank == 52


if __name__ == '__main__':
    main()
