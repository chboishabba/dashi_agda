#!/usr/bin/env python3
"""Exact algebraic tests of classical j-lambda special point identities.

These checks are NOT proofs that the repository's actual analytic modular
function agrees with lambda's rational expression at arbitrary tau or
that the CM class-polynomial identity holds at discriminant -163.

Sources: Klein j and Legendre lambda (classical); Serre, A Course in
Arithmetic (1973); Miyake, Modular Forms (2006).
"""
import sympy as S

x = S.symbols("lambda")

def j_legendre(t):
    return 256 * (1-t+t*t)**3 / (t*t*(1-t)**2)

assert S.cancel(j_legendre(S.Rational(1, 2))-1728)==0

for t in ((1+S.sqrt(-3))/2, (1-S.sqrt(-3))/2):
    assert S.simplify(j_legendre(t))==0

for t in (1-x, 1/x, 1/(1-x), (x-1)/x, x/(x-1)):
    assert S.cancel(j_legendre(x)-j_legendre(t))==0

omega = (-1 + S.sqrt(-3))/2
assert S.simplify(omega**2+omega+1)==0
assert S.simplify((omega+1)**4-1)!=0
assert S.I**6 == -1
assert -640320**3 == -262537412640768000

# For Apéry's a_k = 1/[k^3*C(2k,k)], the inverse-binomial
# hypergeometric ratio (before the 1/k^3 scalar) is
# k^2 / [2k(2k-1)], not k^2 / [4k(2k-1)].
k = S.symbols("k", integer=True, positive=True)
a = lambda k: 1/(k**3*S.binomial(2*k,k))
ratio = S.simplify(S.combsimp(a(k)/a(k-1)))
correct = (k/(2*(2*k-1)))*((k-1)**3/k**3)
incorrect = (k/(4*(2*k-1)))*((k-1)**3/k**3)
assert S.simplify(ratio-correct)==0
assert S.simplify(ratio-incorrect)!=0

print("PASS exact j(lambda) S3 orbit and special algebraic lambda values")
print("PASS integer -163 CM singular value arithmetic (NOT analytic evaluation)")
print("PASS factor-of-two correction in generic Apéry specialization")
