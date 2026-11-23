#!/usr/bin/env python3
"""YM P0: exact periodic-4D tube exterior-leaf geometry + Z3 transfer control.

All source incidences are genuine L^4/4L^4/6L^4 Wilson lattice
sites/links/plaquettes. The finite Z3 transfer experiment checks the
cumulant algebra independently; it is NOT continuous SU(3) Haar or
CMP119/122 physical W3.
"""
from itertools import product, combinations
from fractions import Fraction as Q
from collections import Counter
import sympy as s


def advance(x, a, L):
    y = list(x)
    y[a] = (y[a] + 1) % L
    return tuple(y)


def boundary(p, L):
    x, a, b = p
    return frozenset(((x, a), (advance(x, a, L), b),
                      (advance(x, b, L), a), (x, b)))


def prism(L, d, a, b):
    caps = {((0, 0, 0, 0), a, b), ((d, 0, 0, 0), a, b)}
    walls = set()
    for k in range(d):
        for axis, transverse in ((a, b), (b, a)):
            for offset in (0, 1):
                x = [0]*4
                x[0], x[transverse] = k, offset
                walls.add((tuple(x), 0, axis))
    sections = {((k, 0, 0, 0), a, b) for k in range(d+1)}
    return caps, walls, sections


cases = 0
for L in (3, 4, 5, 6):
    all_faces = {(x, a, b) for x in product(range(L), repeat=4)
                 for a, b in combinations(range(4), 2)}
    assert len(all_faces) == 6*L**4
    for d in range(1, L):
        for a, b in combinations((1, 2, 3), 2):
            caps, walls, sections = prism(L, d, a, b)
            assert len(caps) == 2 and len(walls) == 4*d
            assert len(sections) == d+1
            selected = caps | walls
            support = set().union(*(boundary(p, L) for p in selected))
            assert len(support) == 8*d+4
            incidences = Counter(edge for p in selected for edge in boundary(p, L))
            assert set(incidences.values()) == {2}
            # Survey every actual source plaquette, not only tube candidates.
            # Precisely the d+1 transverse time-sections have no independent
            # Haar-leaf link when one additional H=t_p is inserted.
            inside = {p for p in all_faces if boundary(p, L) <= support}
            assert inside == selected | sections, (L, d, a, b, inside ^ (selected | sections))
            assert len(inside-selected) == d-1
            cases += 1
    print(f"PASS L={L}: 3 transverse planes, all 1<=d<L, full 6L^4 source census")
assert cases == 42
print("PASS 42/42 periodic 4D geometry cases; L4/d2: exactly 3 restored time sections")


# Independent exact cyclic-group transfer test; NOT original SU(3) Haar.
# Use Z3 with t(k)=cos(2pi*k/3), positive weights 5:1:1.
t = [Q(1), Q(-1, 2), Q(-1, 2)]
w = [Q(5, 7), Q(1, 7), Q(1, 7)]
m = sum(w[z]*t[z] for z in range(3))
assert m == Q(4, 7)
P = [[w[(y-x) % 3] for y in range(3)] for x in range(3)]


def multiply(A, B):
    return [[sum(A[i][k]*B[k][j] for k in range(3))
             for j in range(3)] for i in range(3)]


step = multiply(multiply(P, P), multiply(P, P))
assert all(sum(step[x][y]*t[y] for y in range(3)) == m**4*t[x]
           for x in range(3))
mu3 = sum(v**3 for v in t)/3
var = sum(v**2 for v in t)/3
assert mu3 == Q(1, 4) and var == Q(1, 2)
triple = pair = Q(0)
for x0, x1, x2 in product(range(3), repeat=3):
    weight = step[x0][x1]*step[x1][x2]/3
    triple += weight*t[x0]*t[x1]*t[x2]
    pair += weight*t[x0]*t[x2]
assert triple == mu3*m**8 and pair == var*m**8

# Differentiate an independently normalized 3-section finite source.
eps = s.symbols("eps")
Z = EF = EG = EFG = s.Integer(0)
for x0, x1, x2 in product(range(3), repeat=3):
    probability = s.Rational(step[x0][x1]*step[x1][x2], 3)
    weight = probability
    for x in (x0, x1, x2):
        weight *= 1 + eps*s.Rational(t[x])
    Z += weight
    EF += weight*s.Rational(t[x0])
    EG += weight*s.Rational(t[x2])
    EFG += weight*s.Rational(t[x0]*t[x2])
cov = EFG/Z - EF*EG/Z**2
assert s.simplify(s.diff(cov, eps).subs(eps, 0)
                  - 3*s.Rational(mu3)*s.Rational(m)**8) == 0
print("PASS exact independent Z3 transfer and differentiated three-section normalized source")


# Analytic SU(N) results used for the theorem:
# v_N=E_Haar[t^2]; h_N=E_Haar[t^3].
# Center selection annihilates h_N for N!=3. For SU(3), the unique
# epsilon invariant gives integral (Tr U)^3 = 1, hence h_3 = 1/108.
# These are mathematical representation facts, NOT computed Haar integrals.
def haar_variance(N):
    return Q(1, 4) if N == 2 else Q(1, 2*N*N)


def haar_third(N):
    return Q(1, 108) if N == 3 else Q(0)


assert [haar_third(N) for N in range(2, 9)] == [Q(0), Q(1, 108)] + [Q(0)]*5
assert haar_third(3) / haar_variance(3) == Q(1, 6)
print("PASS SU(N) center/epsilon exact rational selection: h_3=1/108, other h_N=0")
print("DERIVED at tau=0: beta*(d+1)*h_N*product_{q in T}m_N(beta_q)")
print("OPEN: any tau>0 bound, CMP119/122 source operation, original full W3 and continuum")
