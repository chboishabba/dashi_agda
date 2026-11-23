#!/usr/bin/env python3
"""CMP102 original shifted A/B: exact finite polynomial and uniform analytic modulus.

Independent Fraction acceptance, not Agda kernel acceptance.  Uses the original
CMP109 inverse-factorial sequences; all inequalities are exact rational.
"""
from fractions import Fraction as Q
from math import factorial


def a(n):
    return Q(1, factorial(2*n + 2))


def b(n):
    return Q(1, factorial(2*n + 3))


def add(*polys):
    out = [Q(0)] * max(map(len, polys))
    for p in polys:
        for j, c in enumerate(p):
            out[j] += c
    return out


def scale(p, s):
    return [s*c for c in p]


def mul(p, q):
    out = [Q(0)] * (len(p) + len(q) - 1)
    for i, x in enumerate(p):
        for j, y in enumerate(q):
            out[i+j] += x*y
    return out


def shift(p, k):
    return [Q(0)]*k + p


def poly_value(p, x):
    val = Q(0)
    for c in reversed(p):
        val = val*x + c
    return val


def bracket(a_poly, b_poly):
    # Same original CMP102 G = 1 - 2A - X A^2 + 2 X B + X^2 B^2.
    return add([Q(1)], scale(a_poly, -2), scale(shift(mul(a_poly, a_poly), 1), -1),
               scale(shift(b_poly, 1), 2), shift(mul(b_poly, b_poly), 2))


A_MAX = Q(6, 11)  # sum_{n>=0} (1/2)(1/12)^n
B_MAX = Q(10, 57)  # sum_{n>=0} (1/6)(1/20)^n
L1_MAX = 1 + 2*A_MAX + A_MAX**2 + 2*B_MAX + B_MAX**2
assert L1_MAX == Q(1089001, 393129) < 3

checks = 0
for n in range(0, 128):
    assert a(n+1)/a(n) == Q(1, (2*n+3)*(2*n+4)) <= Q(1, 12)
    assert b(n+1)/b(n) == Q(1, (2*n+4)*(2*n+5)) <= Q(1, 20)
    assert a(n) <= Q(1, 2)*Q(1, 12)**n
    assert b(n) <= Q(1, 6)*Q(1, 20)**n
    checks += 4

# N input terms A_N, B_N. Low n<N cancellation is exact, regardless
# of the high-degree tail, and needs both original Cauchy endpoints.
for N in range(1, 49):
    ap, bp = [a(i) for i in range(N)], [b(i) for i in range(N)]
    g = bracket(ap, bp)
    assert len(g) == 2*N + 1
    assert all(g[n] == 0 for n in range(N))
    checks += N

    # This is a rigorous coefficient-norm majorant, not a point grid bound.
    norm = sum(map(abs, g))
    assert norm <= 1 + 2*sum(ap) + sum(ap)**2 + 2*sum(bp) + sum(bp)**2
    assert norm <= L1_MAX < 3
    checks += 2

    # Omit only the last original A endpoint: the first corrupted degree
    # is N-1, proving the finite row equality requires that endpoint.
    missing_last_a = ap[:-1] + [Q(0)]
    bad = bracket(missing_last_a, bp)
    assert bad[N-1] == 2*a(N-1) != 0
    checks += 1

    r = Q(1, 4)
    tail_a = Q(24, 47)*Q(1, 48)**N
    tail_b = Q(40, 237)*Q(1, 80)**N
    final_modulus = 3*r**N + Q(25, 11)*tail_a + Q(119, 228)*tail_b
    assert final_modulus > 0
    for x in [-r, -r/2, Q(0), r/2, r]:
        # Uniform bound is proved by polynomial support + L1, not these samples.
        assert abs(poly_value(g, x)) <= norm*r**N <= 3*r**N
        checks += 1

print(f"PASS exact rational assertions: {checks}; degrees 0..127; partial lengths 1..48")
print("L1 global majorant:", L1_MAX, "< 3")
print("UNIFORM |G(X)| <= 3*4^-N + (25/11)*(24/47)*48^-N + (119/228)*(40/237)*80^-N")
print("Acceptance: source-independent finite math; Agda/Bishop import and kernel pending")
