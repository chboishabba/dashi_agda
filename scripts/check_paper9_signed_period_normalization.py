"""Exact reference only; no Agda or Lean acceptance."""
from fractions import Fraction
from math import factorial
import sympy as sp

A, B, K, C = 13591409, 545140134, 426880, 640320**3
D = B - 6*A
t = sp.Rational(C+1728, C)
a = 163*t
m, r, x, y, e, f, j, p = sp.symbols('m r x y e f j p')
assert sp.expand(6*y*(A*f+B*j)-f*(B*x*e-D*y)-B*(6*y*j-f*(e*x-y))) == 0
assert sp.expand(6*m*r*y*(A*f+B*j)-6*B*f*x-(m*r*B*(6*y*j-f*(e*x-y))+f*(m*r*(B*x*e-D*y)-6*B*x))) == 0
assert sp.expand((p*r*y)**2-(B*f*x)**2-(p*p*y*y*(r*r-163)+163*p*p*(y*y-t*x**3)-B*B*x*x*(f*f-x)+(a*p*p-B*B)*x**3)) == 0
assert a*K*K*10005 == B*B
assert sp.Rational(D,B) == sp.Rational(77265280,90856689)
H = J = S = Fraction(0)
for n in range(257):
    u = Fraction((-1)**n*factorial(6*n), C**n*factorial(3*n)*factorial(n)**3)
    c = Fraction(factorial(6*n), 1728**n*factorial(3*n)*factorial(n)**3)
    assert c*Fraction(-1728,C)**n == u
    H += u
    J += n*u
    S += (A+B*n)*u
    assert S == A*H+B*J
    assert abs(u) <= Fraction(1, 2**(41*n))
    assert abs(n*u) <= Fraction(A, 2**(41*n))
    if n:
        assert S != A*H-B*J
# A square-only certificate cannot select the signed period.
assert sp.expand((-p)**2-p**2) == 0
assert sp.expand((-p)*r*y-B*f*x-(p*r*y-B*f*x)) == -2*p*r*y
print('PASS: 5 symbolic identities, 257 factorial/CM/split/bound stages, 256 sign controls, 2 square-sign controls')
