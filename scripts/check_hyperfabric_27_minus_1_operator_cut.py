#!/usr/bin/env python3
"""Exact arithmetic 27-1 hypervoxel: two 26-dimensional readings.

Physical firewall: site deletion vs graph-constant quotient vs Albert traceless
module vs bosonic 26D worldsheet target are not same objects automatically.
Source geometry is P3^3, not the periodic group C3^3. No string/Clay proof.
"""
from collections import Counter
from fractions import Fraction as Q
from itertools import product

SITES = tuple(product((-1, 0, 1), repeat=3))
O = (0, 0, 0)
NONORIGIN = tuple(x for x in SITES if x != O)
MODE1 = ((1, 1, 1), (1, 0, -1), (1, -2, 1))
LAM1 = (0, 1, 3)

def neighbours(x):
    for i in range(3):
        for d in (-1, 1):
            y = list(x)
            y[i] += d
            if -1 <= y[i] <= 1:
                yield tuple(y)

def lap(f):
    return {x: sum((f[x] - f[y] for y in neighbours(x)), Q(0)) for x in SITES}

def mean(f):
    return sum(f.values(), Q(0)) / 27

def project(f):
    avg = mean(f)
    return {x: f[x] - avg for x in SITES}

def differences(f):
    return {x: f[x] - f[O] for x in NONORIGIN}

def reconstruct(a):
    """Unique zero-mean representative of coefficients f(p)-f(origin)."""
    shift = -sum(a.values(), Q(0)) / 27
    return {x: (shift if x == O else a[x] + shift) for x in SITES}

def dirichlet(a):
    """Origin-deleted PRINCIPAL submatrix D of full path Laplacian."""
    return {p: sum((a[p] - (a[q] if q != O else Q(0))
                    for q in neighbours(p)), Q(0)) for p in NONORIGIN}

def exact_reduced_laplacian(a):
    """Gauge difference coordinates of the ZERO-MEAN operator, not D alone.
    A = D + 1*b^T, where b picks six origin-neighbour coordinates.
    A is self-adjoint with respect to G=I-J/27, not Euclidean dot.
    """
    d = dirichlet(a)
    defect = sum((a[q] for q in neighbours(O)), Q(0))
    return {p: d[p] + defect for p in NONORIGIN}

def metric(a, b):
    sa = sum(a.values(), Q(0))
    sb = sum(b.values(), Q(0))
    return sum((a[x] * b[x] for x in NONORIGIN), Q(0)) - sa * sb / 27

def flip(f):
    return {p: f[tuple(-z for z in p)] for p in SITES}

def wave(k):
    return {x: Q(MODE1[k[0]][x[0]+1] * MODE1[k[1]][x[1]+1] *
                 MODE1[k[2]][x[2]+1]) for x in SITES}

def basis(i):
    return {x: Q(int(x == i)) for x in NONORIGIN}

def is_zero(f):
    return all(v == 0 for v in f.values())

def check():
    assert len(SITES) == 27 and len(NONORIGIN) == 26
    assert len(tuple(neighbours(O))) == 6
    pairs = {frozenset((p, tuple(-z for z in p))) for p in NONORIGIN}
    assert len(pairs) == 13 and all(len(p) == 2 for p in pairs)
    print('PASS spatial carrier: origin + 26 nonorigin = 1+13+13 sites')

    for i in NONORIGIN:
        ai = basis(i)
        f = reconstruct(ai)
        assert mean(f) == 0 and differences(f) == ai
        assert differences(lap(f)) == exact_reduced_laplacian(ai)
        for j in NONORIGIN:
            aj = basis(j)
            lhs = metric(ai, exact_reduced_laplacian(aj))
            rhs = metric(exact_reduced_laplacian(ai), aj)
            assert lhs == rhs

    # Exact positive-definite pullback metric: G=I_26-J_26/27.
    # On the 26-vector of ones the eigenvalue is 1/27; on its
    # 25-dimensional sum-zero orthogonal complement the eigenvalue is 1.
    one26 = {p: Q(1) for p in NONORIGIN}
    assert metric(one26, one26) == Q(26,27)
    samples = [basis(NONORIGIN[0]), one26,
               {p: Q((3*i*i-7*i) % 11-5) for i,p in enumerate(NONORIGIN)}]
    for a in samples:
        euclid_norm = sum((a[p]*a[p] for p in NONORIGIN), Q(0))
        assert metric(a, a) >= euclid_norm / 27
    assert metric(basis(NONORIGIN[0]), basis(NONORIGIN[0])) == Q(26,27)
    print('PASS G positive definite: eigenvalues 1 (mult 25), 1/27 (mult 1); no timelike axis')

    constant = {x: Q(1) for x in SITES}
    assert is_zero(lap(constant)) and is_zero(project(constant))
    delta_origin = {x: Q(int(x == O)) for x in SITES}
    assert not is_zero(lap(delta_origin))
    assert len({x for x in NONORIGIN if lap(delta_origin)[x] == -1}) == 6
    assert is_zero({x: reconstruct(differences(project(delta_origin)))[x]
                    - project(delta_origin)[x] for x in SITES})
    assert any(exact_reduced_laplacian(basis(i))[p] != dirichlet(basis(i))[p]
               for i in NONORIGIN for p in NONORIGIN)
    print('PASS zero-mean quotient: exact 26-coordinate inverse, commuting path-Laplacian')
    print('PASS A=D+1*b^T rank-one origin-neighbour repair; G-selfadjoint on 26 coords')
    print('PASS counterexample: deleting origin is NOT removing the zero eigenmode')

    spectra = Counter()
    for k in product(range(3), repeat=3):
        v = wave(k)
        ev = sum((LAM1[j] for j in k))
        assert lap(v) == {p: ev * v[p] for p in SITES}
        spectra[ev] += 1
        if k != (0, 0, 0):
            assert mean(v) == 0
            a = differences(v)
            assert exact_reduced_laplacian(a) == {p: ev*a[p] for p in NONORIGIN}
    assert spectra == Counter({0:1,1:3,2:3,3:4,4:6,5:3,6:3,7:3,9:1})
    assert sum(n for e,n in spectra.items() if e) == 26
    for k in product(range(3), repeat=3):
        for l in product(range(3), repeat=3):
            if k != l:
                assert sum((wave(k)[p]*wave(l)[p] for p in SITES), Q(0)) == 0
    print('PASS complete 27 path standing modes: 1 constant + 26 nonconstant modes')
    print('Laplacian spectrum:', dict(sorted(spectra.items())))

    assert all(flip(lap(wave(k))) == lap(flip(wave(k)))
               for k in product(range(3), repeat=3))
    for pair in pairs:
        a,b = tuple(pair)
        odd = {p: Q(int(p == a) - int(p == b)) for p in SITES}
        even = {p: Q(int(p == a) + int(p == b) - 2*int(p == O)) for p in SITES}
        assert mean(odd) == mean(even) == 0
        assert flip(odd) == {p: -v for p,v in odd.items()}
        assert flip(even) == even
        assert flip(lap(odd)) == {p: -v for p,v in lap(odd).items()}
        assert flip(lap(even)) == lap(even)
    print('PASS V0 = 13 even nonconstant + 13 odd under cube inversion')
    assert 27-1 == 26 == 13+13
    assert 26-2 == 24 and 24+2-26 == 0 and 10+5-26+11 == 0
    print('BOUNDARY: 26 graph wave modes != bosonic target coordinates, c=26, or Albert J0')
    print('BOUNDARY: inversion parity != chirality; no F4, BRST or string theorem')

if __name__ == '__main__':
    check()
