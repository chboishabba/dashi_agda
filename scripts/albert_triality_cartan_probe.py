#!/usr/bin/env python3
"""Exact Cartan/chirality probe for the Albert 28+8+8+8 triality split.

Uses the integer-cleared structure constants from albert_inner_derivation_rank.
The four Cartan generators are the inner commutators associated with coordinate
pairs (3,4), (5,6), (7,8), (9,10), i.e. the four orthogonal rotations in the
first octonion slot.

If N_k = 4 H_k is the integer-cleared derivation matrix, this checks exactly:

* x-slot: N_k/4 is the standard rotation in one of four orthogonal 2-planes;
* y,z slots: N_k^2 = -4 I, hence H_k^2 = -1/4 I;
* all four Cartan operators commute;
* product_k N_k = +16 I on y and -16 I on z,
  equivalently product_k (2H_k) = +I / -I.

Thus x is the vector 8, while y and z are the two chiral half-spin 8s.
"""

import numpy as np
from albert_inner_derivation_rank import N, jordan_times_two


def main():
    basis = np.eye(N, dtype=np.int64)
    C2 = np.zeros((N,N,N), dtype=np.int64)
    for i in range(N):
        for j in range(N):
            C2[:,i,j] = jordan_times_two(basis[i], basis[j])
    L2 = np.transpose(C2, (1,0,2))

    def comm(i,j):
        return L2[i] @ L2[j] - L2[j] @ L2[i]

    cartan_pairs = [(3,4),(5,6),(7,8),(9,10)]
    cartan = [comm(i,j) for i,j in cartan_pairs]  # each is N_k = 4 H_k

    slots = {
        'x': list(range(3,11)),
        'y': list(range(11,19)),
        'z': list(range(19,27)),
    }

    # The x-slot restrictions are exactly four standard plane rotations * 4.
    for k,D in enumerate(cartan):
        block = D[np.ix_(slots['x'],slots['x'])]
        expected = np.zeros((8,8), dtype=np.int64)
        i,j = 2*k,2*k+1
        expected[i,j] = 4
        expected[j,i] = -4
        if not np.array_equal(block, expected):
            raise AssertionError(f'x vector Cartan block {k} mismatch')

    # Cartan commutation on the complete 27-dimensional Albert representation.
    for A in cartan:
        for B in cartan:
            if not np.array_equal(A @ B, B @ A):
                raise AssertionError('Cartan generators do not commute')

    for name,chirality in [('y',+1),('z',-1)]:
        ids = slots[name]
        blocks = [D[np.ix_(ids,ids)] for D in cartan]
        I8 = np.eye(8,dtype=np.int64)
        for B in blocks:
            if not np.array_equal(B @ B, -4*I8):
                raise AssertionError(f'{name}: expected N_k^2 = -4 I')
        product = np.eye(8,dtype=np.int64)
        for B in blocks:
            product = product @ B
        if not np.array_equal(product, chirality*16*I8):
            raise AssertionError(f'{name}: chirality mismatch')

    print('cartan_dimension=4')
    print('x_role=vector_8')
    print('y_role=half_spin_plus_8')
    print('z_role=half_spin_minus_8')
    print('spin_cartan_square=H_k^2=-1/4I')
    print('spin_chirality=+1,-1')
    print('triality_weight_root_ledger=24+8+8+8=48')
    print('derivation_dimension_ledger=4+48=52')


if __name__ == '__main__':
    main()
