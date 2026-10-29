"""Universal quadratic spectral coefficient certificate (finite exact roots).

This is a basis-level proof audit, not finite random testing, Agda kernel proof,
physical Navier--Stokes evolution, optical-clock data, or Monster evidence.
The C4 character is in Q(i); the C5 character is in Q(zeta_5).
Orszag/Patterson own the classical pseudo-spectral/dealiasing mathematics.
"""
from itertools import product

K = tuple(product((-1, 0, 1), repeat=3))
W = tuple(product((-2, -1, 0, 1, 2), repeat=3))
GRID4 = tuple(product(range(4), repeat=3))


def phase5(n):
    n %= 5
    if n == 4:
        return (-1, -1, -1, -1)
    return tuple(int(i == n) for i in range(4))


def sum5(k):
    return tuple(sum(phase5(k*x)[j] for x in range(5)) for j in range(4))


def sum4(k):
    # Exact Gaussian integer as a pair (real,imaginary).
    phases = ((1, 0), (0, 1), (-1, 0), (0, -1))
    return tuple(sum(phases[(k*x) % 4][j] for x in range(4)) for j in range(2))


def c4_kernel(diff):
    parts = [sum4(n) for n in diff]
    # Each axis character sum is 4 or 0. Product gives 64 delta.
    assert all(a in ((4, 0), (0, 0)) for a in parts)
    return int(all(a == (4, 0) for a in parts))


def c5_kernel(diff):
    parts = [sum5(n) for n in diff]
    assert all(a in ((5, 0, 0, 0), (0, 0, 0, 0)) for a in parts)
    return int(all(a == (5, 0, 0, 0) for a in parts))


def certificate():
    # All one-dimensional C4 and C5 root sums, not sampled profiles.
    assert [sum4(d) for d in range(4)] == [(4, 0), (0, 0), (0, 0), (0, 0)]
    assert [sum5(d) for d in range(5)] == [(5, 0, 0, 0)] + [(0, 0, 0, 0)] * 4

    # Every entry of the 64x64 C4 forward/inverse matrix composition.
    for k in GRID4:
        for l in GRID4:
            diff = tuple(a - b for a, b in zip(k, l))
            assert c4_kernel(diff) == int(k == l)

    c4_cases = 0
    c5_cases = 0
    for p in K:
        for q in K:
            exact = tuple(a + b for a, b in zip(p, q))
            for k in K:
                # Coefficients of arbitrary symbolic u[p]*v[q].
                diff = tuple(s-t for s, t in zip(exact, k))
                assert c4_kernel(diff) == int(exact == k)
                c4_cases += 1
            for k in W:
                diff = tuple(s-t for s, t in zip(exact, k))
                assert c5_kernel(diff) == int(exact == k)
                c5_cases += 1
    assert c4_cases == 27 * 27 * 27 == 19683
    assert c5_cases == 27 * 27 * 125 == 91125

    # C4 loses full quadratic output: +2 and -2 yield same residue.
    assert 2 % 4 == (-2) % 4
    assert all((s-k) % 4 != 0 for k in (-1, 0, 1)
               for s in (-2, 2))

    # Nyquist corners: every coordinate fixed under negation is 0 or 2.
    fixed4 = [k for k in GRID4 if all((-x) % 4 == x for x in k)]
    assert len(fixed4) == 8

    print('PASS: C4 4096 inverse/forward delta entries, 19683 universal bilinear basis coefficients')
    print('PASS: C5 91125 universal bilinear basis coefficients at all 125 full outputs')
    print('PASS: 8 C4 Nyquist fixed corners; C4 cannot recover full +-2 output')


if __name__ == '__main__':
    certificate()
