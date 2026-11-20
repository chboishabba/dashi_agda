"""Exact finite regressions for normalized bounded tests, not a continuum proof."""
import sympy as s
from itertools import product
checks = 0
def check(p):
    global checks
    assert p
    checks += 1
w = [s.Rational(1,7), s.Rational(2,7), s.Rational(4,7)]
x = [-s.S.One, s.Rational(1,3), s.Rational(3,4)]
for beta, radius in product([s.Rational(0), s.Rational(1,3), s.Rational(2)], [s.Rational(1,10), s.Rational(1), s.Rational(3)]):
    # Positive polynomial Gibbs surrogate, deliberately not Haar Wilson.
    a = [p*(1+beta*v*v) for p,v in zip(w,x)]
    z = sum(a)
    E = lambda f: sum(p*f(v) for p,v in zip(a,x))/z
    check(E(lambda v:1)==1)
    for n in range(9):
        check(E(lambda v:abs(v)**n)<=1)
        P = lambda v: sum((radius*abs(v))**j/s.factorial(j) for j in range(n+1))
        upper = P(1)
        check(E(P)<=upper)
        check(z*upper-sum(p*P(v) for p,v in zip(a,x))==sum(p*(upper-P(v)) for p,v in zip(a,x)))
        check(E(lambda v:abs(v)**n)*radius**n/s.factorial(n)<=E(P))
print(f'PASS: {checks} exact rational assertions')
