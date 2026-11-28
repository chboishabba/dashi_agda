"""Exact CM cubic/guarded Klein quotient and selected real-q chart checks."""
from fractions import Fraction
from hashlib import sha1
from pathlib import Path
import sympy as sp

C = 640320**3
t = sp.Rational(C+1728,C)
u,v,d,w,j,r = sp.symbols('u v d w j r')
assert sp.expand(v-u-sp.Rational(1728,C)*(-C)*((u-v)/1728)) == 0
assert sp.expand((-C)*(u-t*u)/1728-u) == 0
assert sp.expand((u*w)*d-u-u*(d*w-1)) == 0
assert sp.expand((-r)**2+0**2-r*r) == 0
# Retain the imaginary zero coordinate and both signs of q in powers.
for n in range(257):
    q = -Fraction(1,2**36)
    assert q**n == (-1)**n*abs(q)**n
    assert (q**n).denominator == 2**(36*n)
    if n%2:
        assert q**n != abs(q)**n
# Guarded quotient is an equivalence on nonzero literal discriminants.
for i in range(1,65):
    x3=Fraction(i, i+1)
    for shift in (-1,0,1):
        y2=Fraction(C+1728,C)*x3+Fraction(shift,C)
        delta=(x3-y2)/1728
        if delta >= 0:
            continue
        j=x3/delta
        assert (j == -C) == (y2 == Fraction(C+1728,C)*x3)
        assert j*delta == x3
assert (Fraction(1)-Fraction(1))/1728 == 0
# A square/norm alone cannot distinguish the two real q charts.
assert (-Fraction(1,2**36))**2 == Fraction(1,2**36)**2
assert -Fraction(1,2**36) != Fraction(1,2**36)
b=Path(__file__).read_bytes()
print('PASS: 4 symbolic identities; 257 signed power stages; 128 odd sign controls; 192 guarded quotient cases; 2 boundary controls')
print('git blob',sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest())
