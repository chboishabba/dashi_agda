#!/usr/bin/env python3
"""Observer-indexed exact finite Hamiltonian reduction (Schur/Feshbach).

The compressed observer sees P-sector. H=[A B; B^T D].
The exact projected resolvent retains Sigma(z)=B(zI-D)^-1 B^T.
Finite rational models only: not a 5D KK action, electron, or quantum chemistry derivation.
"""
from itertools import product
import sympy as sp


def model(a, d, v, w):
    """One observed radial state, two hidden compact modes."""
    A = sp.Matrix([[a]])
    D = sp.diag(d, d + w)
    B = sp.Matrix([[v, 2*v]])
    return A, B, D


def check_model(A, B, D, z):
    n, m = A.rows, D.rows
    H = A.row_join(B).col_join(B.T.row_join(D))
    P = sp.eye(n).col_join(sp.zeros(m, n))
    full = (z*sp.eye(n+m)-H).inv()
    sigma = B*(z*sp.eye(m)-D).inv()*B.T
    effective = (z*sp.eye(n)-A-sigma).inv()
    assert P.T*full*P == effective
    assert H == H.T
    # Naive PHP resolvent is wrong if removed modes couple to P.
    if any(x != 0 for x in B):
        assert effective != (z*sp.eye(n)-A).inv()
    # Effective operator at different energy is not a constant correction.
    return H, sigma, effective


def main():
    cases = 0
    for a, d, v, w, z in product((1, 2), (4, 5), (1, 2), (1, 2), (-1, 0, 3)):
        A, B, D = model(a, d, v, w)
        H, sigma, projected = check_model(A, B, D, sp.Integer(z))
        assert sigma != B*(sp.Integer(z-1)*sp.eye(2)-D).inv()*B.T
        cases += 1
    # Exactly decoupled modes: naive projection IS valid.
    A, _, D = model(1, 4, 2, 1)
    zero = sp.zeros(1, 2)
    _, sig0, exact0 = check_model(A, zero, D, sp.Integer(-1))
    assert sig0 == sp.zeros(1, 1)
    assert exact0 == (sp.Integer(-1)*sp.eye(1)-A).inv()
    # Same observed A and D, different hidden couplings => distinct spectra.
    A, B, D = model(1, 4, 1, 1)
    H0 = A.row_join(zero).col_join(zero.T.row_join(D))
    H1 = A.row_join(B).col_join(B.T.row_join(D))
    assert H0[:1, :1] == H1[:1, :1]
    assert H0.charpoly().as_expr() != H1.charpoly().as_expr()
    # Minimal observer residual for the declared projected-resolvent consumer:
    # (A,D) alone cannot decide it; B-dependent Sigma(z) suffices exactly.
    z = sp.Integer(-1)
    sigma = B*(z*sp.eye(2)-D).inv()*B.T
    assert sigma != sp.zeros(1,1)
    assert (z*sp.eye(1)-A-sigma).inv() == (z*sp.eye(3)-H1).inv()[:1, :1]
    # An independent unitary change of hidden coordinates preserves projected response.
    U = sp.Matrix([[0, 1],[-1,0]])
    D2 = U.T*D*U
    B2 = B*U
    assert B2*(z*sp.eye(2)-D2).inv()*B2.T == sigma
    print(f'PASS {cases}/48 exact observer-indexed Schur/resolvent commutations')
    print('PASS decoupled-mode case, coupled-mode negative control, distinct spectra, hidden-frame invariance')
    print('OPEN empirical 369/KK source-to-H derivation, dynamical calibration, exact Agda kernel')


if __name__ == '__main__':
    main()
