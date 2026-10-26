#!/usr/bin/env python3
"""Exact inner-derivation / triality audit for the rational Albert algebra.

This mirrors the coordinate convention in
DASHI/Mathematics/Algebra/RationalAlbertJordanProductExact.agda.

All structure constants are stored after multiplication by 2, so they are
integers.  If L_i is left Jordan multiplication by coordinate basis vector e_i,
then 4[L_i,L_j] is an integer 27x27 matrix.  The script:

* constructs all nonzero inner commutators;
* verifies the derivation law exactly on every coordinate-basis product;
* computes their exact Q-rank over ZZ;
* checks the explicit independent 52-element basis split 28+8+8+8;
* verifies the exact triality bracket-containment pattern;
* verifies that the 28-sector acts block-diagonally on the three octonion
  slots and restricts to a full 28-dimensional skew algebra on each slot.

No floating-point or finite-field rank is used for the reported certificates.
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


def exact_rank(matrices):
    rows = [[int(x) for x in M.reshape(-1)] for M in matrices]
    if not rows:
        return 0
    return sp.polys.matrices.DomainMatrix.from_list(rows, sp.ZZ).rank()


def main():
    basis = np.eye(N, dtype=np.int64)
    C2 = np.zeros((N,N,N), dtype=np.int64)
    for i in range(N):
        for j in range(N):
            C2[:,i,j] = jordan_times_two(basis[i], basis[j])

    # L2[i] = 2*L_{e_i}; hence D_ij below equals 4[L_i,L_j].
    L2 = np.transpose(C2, (1,0,2))
    commutators = {}
    for i,j in combinations(range(N),2):
        Dij = L2[i] @ L2[j] - L2[j] @ L2[i]
        if np.any(Dij):
            commutators[(i,j)] = Dij

    # Exact derivation identity after clearing common denominator 8:
    # D C(x,y) = C(Dx,y) + C(x,Dy).
    for pair,D in commutators.items():
        lhs = np.einsum('ka,aij->kij',D,C2,dtype=np.int64)
        rhs1 = np.einsum('ai,kaj->kij',D,C2,dtype=np.int64)
        rhs2 = np.einsum('aj,kia->kij',D,C2,dtype=np.int64)
        if not np.array_equal(lhs, rhs1 + rhs2):
            raise AssertionError(f'derivation law failed for pair {pair}')

    full_rank = exact_rank(list(commutators.values()))

    # A natural exact basis selected by coordinate sector:
    #   so8 : all C(8,2) commutators inside the x-octonion slot;
    #   V1  : one diagonal idempotent against x (8);
    #   V2  : another idempotent against y (8);
    #   V3  : the same idempotent against z (8).
    sectors = {
        'so8': [(i,j) for i,j in combinations(range(3,11),2)],
        'V1':  [(1,j) for j in range(3,11)],
        'V2':  [(0,j) for j in range(11,19)],
        'V3':  [(0,j) for j in range(19,27)],
    }
    selected_pairs = sectors['so8'] + sectors['V1'] + sectors['V2'] + sectors['V3']
    selected = [commutators[p] for p in selected_pairs]
    selected_rank = exact_rank(selected)

    assert len(sectors['so8']) == 28
    assert len(sectors['V1']) == len(sectors['V2']) == len(sectors['V3']) == 8
    assert len(selected_pairs) == 52
    assert selected_rank == 52
    assert full_rank == 52

    # Triality bracket-containment table.  Containment is checked exactly by
    # verifying that adjoining all relevant brackets does not increase the exact
    # ZZ/Q rank of the proposed target sector.
    target = {
        ('so8','so8'): 'so8',
        ('so8','V1'): 'V1', ('so8','V2'): 'V2', ('so8','V3'): 'V3',
        ('V1','V1'): 'so8', ('V2','V2'): 'so8', ('V3','V3'): 'so8',
        ('V1','V2'): 'V3', ('V2','V3'): 'V1', ('V3','V1'): 'V2',
    }

    sector_matrices = {name:[commutators[p] for p in pairs] for name,pairs in sectors.items()}
    for (left,right),out in target.items():
        brackets = []
        for A in sector_matrices[left]:
            for B in sector_matrices[right]:
                K = A @ B - B @ A
                if np.any(K):
                    brackets.append(K)
        out_basis = sector_matrices[out]
        if exact_rank(out_basis + brackets) != exact_rank(out_basis):
            raise AssertionError(f'bracket containment failed: [{left},{right}] <= {out}')

    # The 28-sector acts block-diagonally on x,y,z; every restriction is a
    # 28-dimensional algebra of skew 8x8 matrices.
    slots = {'x':list(range(3,11)), 'y':list(range(11,19)), 'z':list(range(19,27))}
    so8_mats = sector_matrices['so8']
    for D in so8_mats:
        # no diagonal or cross-slot action
        mask = np.zeros((N,N), dtype=bool)
        for ids in slots.values():
            mask[np.ix_(ids,ids)] = True
        if np.any(D[~mask]):
            raise AssertionError('so8 sector is not block diagonal on octonion slots')
    for name,ids in slots.items():
        blocks = [D[np.ix_(ids,ids)] for D in so8_mats]
        if not all(np.array_equal(B.T,-B) for B in blocks):
            raise AssertionError(f'{name} restriction not skew')
        if exact_rank(blocks) != 28:
            raise AssertionError(f'{name} restriction rank not 28')

    print(f'coordinate_dimension={N}')
    print(f'basis_products_checked={N*N}')
    print(f'nonzero_inner_commutators={len(commutators)}')
    print('all_inner_commutators_derivations=true')
    print(f'exact_rational_span_rank={full_rank}')
    print('selected_basis_split=28+8+8+8')
    print(f'selected_basis_rank={selected_rank}')
    print('so8_three_slot_restrictions=skew_rank_28')
    print('triality_bracket_pattern=true')

    assert len(commutators) == 324
    assert full_rank == 52


if __name__ == '__main__':
    main()
