#!/usr/bin/env python3
"""Exact-rational certificate for a *conditional* original level-32 eta tail bound.

Original curve: E : y^2 = x^3 - x, conductor 32, CM by Z[i].
f32(i t) = exp(-2 pi t) * Product_{n>=1}
    (1 - exp(-8 pi n t))^2 * (1 - exp(-16 pi n t))^2.

The proof of this analytical identity (Dedekind eta) and the ORIGINAL
E32 Mellin identity L(E,1)=4*pi*integral_{1/sqrt(32)}^inf f32(it)dt
are CLASSICAL INPUTS, not established by this finite script.

Exact rational argument:
pi>3; sqrt(2)>7/5; exp(sum-to-8 (21/5)^k/k!)>64, so
r=exp(-8 pi t)<=exp(-pi sqrt2)<1/64 for t>=1/sqrt(32).
For 0<=a_k<=1, Product(1-a_k)>=1-Sum(a_k). Thus the two
eta factors satisfy bounds 62/63 and 4094/4095 respectively.
C=(62/63)^2*(4094/4095)^2.
Then f32(it)>= C exp(-2 pi t) and, assuming the original
Mellin identity, L(E,1)>=2*C*exp(-pi/(2 sqrt2))>0.

No Agda/Lean kernel acceptance or proof of modularity/Mellin is claimed.
"""
from fractions import Fraction
from math import exp, factorial, pi, sqrt, prod

x = Fraction(21, 5)
taylor8 = sum(x**k / factorial(k) for k in range(9))
assert taylor8 == Fraction(16205908927, 250000000)
assert taylor8 - 64 == Fraction(205908927, 250000000)
assert Fraction(7, 5)**2 < 2
C = (Fraction(62, 63)**2) * (Fraction(4094, 4095)**2)
assert C == Fraction(64428653584, 66556260225)
assert 0 < C < 1

# Finite exact elementary product inequality, including zero and equality
# edge cases; the infinite passage is standard monotone convergence.
for r in (Fraction(0), Fraction(1, 64), Fraction(1, 128), Fraction(1, 256)):
    for N in (0, 1, 2, 5, 12):
        one = prod((1-r**k for k in range(1, N+1)), start=Fraction(1))
        two = prod((1-r**(2*k) for k in range(1, N+1)), start=Fraction(1))
        assert one >= 1-sum((r**k for k in range(1, N+1)), Fraction(0))
        assert two >= 1-sum((r**(2*k) for k in range(1, N+1)), Fraction(0))
        assert one >= Fraction(62, 63)
        assert two >= Fraction(4094, 4095)

t0 = 1/sqrt(32)
assert exp(-8*pi*t0) < 1/64
for t in (t0, 0.2, 0.25, 0.4, 0.75, 1.0, 2.0, 5.0):
    r = exp(-8*pi*t)
    # Numerical diagnostic only; analytic inequality is above.
    finite_eta = exp(-2*pi*t)*prod(
        (1-r**n)**2*(1-r**(2*n))**2 for n in range(1, 101)
    )
    assert finite_eta >= float(C)*exp(-2*pi*t)*(1-1e-13)
bound = 2*float(C)*exp(-pi/(2*sqrt(2)))
assert 0.63 < bound < 0.65
print("PASS exact exp lower Taylor-8:", taylor8)
print("PASS exact eta rational factor constant:", C)
print("PASS 40 rational finite-product checks and 8 numerical point diagnostics")
print("Conditional original E32 central L(E,1) bound =", f"{bound:.15f}")
print("CONDITIONAL on authentic eta infinite product and SAME-E32 Mellin identity")
print("No Agda/Lean kernel result or universal BSD conclusion.")
