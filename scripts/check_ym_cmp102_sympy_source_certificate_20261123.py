#!/usr/bin/env python3
"""Exact SymPy CMP102 original A/B certificate (not an Agda/Lean kernel proof).

Same source a[n]=1/(2n+2)!, b[n]=1/(2n+3)!, original |X|<=1/4.
Run locally: python scripts/check_ym_cmp102_sympy_source_certificate_20261123.py
"""
from fractions import Fraction as F
from functools import lru_cache
from math import factorial, comb
import sympy as s

n, k, z = s.symbols('n k z', integer=True, nonnegative=True)
checks = dict(symbolic=0, coefficients=0, polynomials=0, bounds=0, samples=0, controls=0)

# A single symbolic binomial identity at generic n, not a finite extrapolation.
assert s.summation((-1)**k * s.binomial(2*n+2, k), (k, 0, 2*n+2)) == 0
checks['symbolic'] += 1
E, O = s.cosh(z), s.sinh(z)/z
A, B = (E-1)/z**2, (O-1)/z**2
G = 1-2*A-z**2*A**2+2*z**2*B+z**4*B**2
for eq in [z**2*G-(1-E**2+z**2*O**2), E**2-s.sinh(z)**2-1, G]:
    assert s.simplify(eq) == 0
    checks['symbolic'] += 1
assert s.limit(s.simplify(G), z, 0) == 0
checks['symbolic'] += 1

@lru_cache(None)
def a(i): return F(1, factorial(2*i+2))
@lru_cache(None)
def b(i): return F(1, factorial(2*i+3))

def add(*ps):
    out = [F(0)]*max(map(len, ps))
    for p in ps:
        for j, v in enumerate(p): out[j] += v
    return out

def mul(p, q):
    out = [F(0)]*(len(p)+len(q)-1)
    for i, v in enumerate(p):
        for j, w in enumerate(q): out[i+j] += v*w
    return out

def shift(p, i): return [F(0)]*i + p

def bracket(ap, bp):
    return add([F(1)], [-2*x for x in ap],
               [-x for x in shift(mul(ap, ap), 1)],
               [2*x for x in shift(bp, 1)], shift(mul(bp, bp), 2))

def evalpoly(poly, x):
    v = F(0)
    for c in reversed(poly): v = v*x+c
    return v

# Exact original even and odd endpoint decompositions, 128 degrees.
for i in range(128):
    m = i+1
    even = 2*a(i)+sum((a(j)*a(i-1-j) for j in range(i)), F(0))
    odd = F(1) if i == 0 else 2*b(i-1)+sum((b(j)*b(i-2-j) for j in range(i-1)), F(0))
    even_cauchy = sum((F(1, factorial(2*j)*factorial(2*m-2*j)) for j in range(m+1)), F(0))
    odd_cauchy = sum((F(1, factorial(2*j+1)*factorial(2*m-2*j-1)) for j in range(m)), F(0))
    assert even == even_cauchy; assert odd == odd_cauchy
    assert even == odd
    assert sum((-1)**j*comb(2*m,j) for j in range(2*m+1)) == 0
    checks['coefficients'] += 4
    assert a(i+1)/a(i) == F(1,(2*i+3)*(2*i+4)) <= F(1,12)
    assert b(i+1)/b(i) == F(1,(2*i+4)*(2*i+5)) <= F(1,20)
    assert a(i) <= F(1,2)*F(1,12)**i
    assert b(i) <= F(1,6)*F(1,20)**i
    checks['bounds'] += 4

AMAX, BMAX = F(6,11), F(10,57)
L1 = 1+2*AMAX+AMAX**2+2*BMAX+BMAX**2
assert L1 == F(1089001,393129) < 3
assert 2+F(1,4)*2*AMAX == F(25,11)
assert F(1,2)+F(1,16)*2*BMAX == F(119,228)
assert F(1,2)/(1-F(1,48)) == F(24,47)
assert F(1,6)/(1-F(1,80)) == F(40,237)
checks['bounds'] += 5

for N in range(1,49):
    ap,bp = [a(i) for i in range(N)],[b(i) for i in range(N)]
    poly = bracket(ap,bp)
    assert len(poly) == 2*N+1
    assert all(c == 0 for c in poly[:N])
    assert poly[N] == 2*a(N)
    assert sum(map(abs,poly)) <= 1+2*sum(ap)+sum(ap)**2+2*sum(bp)+sum(bp)**2 <= L1
    checks['polynomials'] += N+2
    assert bracket(ap[:-1]+[F(0)],bp)[N-1] == 2*a(N-1) != 0
    checks['controls'] += 1
    for x in [F(-1,4),F(-1,8),F(0),F(1,8),F(1,4)]:
        assert abs(evalpoly(poly,x)) <= sum(map(abs,poly))*F(1,4)**N <= 3*F(1,4)**N
        checks['samples'] += 1

# The N-uniform original Bishop-series modulus is explicit and effective.
for N in [1,2,4,8,16,32,64,128]:
    M = 3*F(1,4)**N + F(25,11)*F(24,47)*F(1,48)**N + F(119,228)*F(40,237)*F(1,80)**N
    assert F(0) < M < 4*F(1,4)**N
    checks['bounds'] += 1

print('PASS SymPy',s.__version__,':',sum(checks.values()),'exact assertion groups',checks)
print('ALL-N Cauchy binomial coefficient = 0, X*G=0, G(0)=0')
print('Original |X|<=1/4 uniform modulus: 3*4^-N + (25/11)*(24/47)*48^-N + (119/228)*(40/237)*80^-N')
print('Agda kernel/import safety, physical T/W3/OS: NOT CERTIFIED')
