#!/usr/bin/env python3
"""YM W0: exact sharp four-column SU(N) Wilson/F19 positive-fibre cone.

This is a NECESSARY diagnostic on any positive SU(N) original Wilson
fine-mark source, not a producer of CMP119 T-steps or physical W3 rates.
Normalize each Wilson plaquette deficit J=1-ReTr(U)/N in [0,2].
Fractions: 255 rational four-corner positive laws, exact covariance/
positive-semidefinite moment and complex-radius tests.
"""
from fractions import Fraction
from itertools import product
import sympy as S

corners=((0,0),(0,2),(2,0),(2,2))
checked=0
for weights in product(range(4),repeat=4):
    z=sum(weights)
    if not z:
        continue
    f=sum(w*a for w,(a,b) in zip(weights,corners))
    g=sum(w*b for w,(a,b) in zip(weights,corners))
    fg=sum(w*a*b for w,(a,b) in zip(weights,corners))
    ff=sum(w*a*a for w,(a,b) in zip(weights,corners))
    gg=sum(w*b*b for w,(a,b) in zip(weights,corners))
    assert 0<=f<=2*z
    assert 0<=g<=2*z
    assert max(0,2*f+2*g-4*z)<=fg<=min(2*f,2*g)
    assert (z*fg-f*g)**2 <= (z*ff-f*f)*(z*gg-g*g)
    conditional_c=Fraction(fg,z)-Fraction(f*g,z*z)
    assert -1<=conditional_c<=1
    checked+=1
assert checked==255

# Sharp conditional covariance endpoints, both with positive K0.
assert Fraction(4,2)-Fraction(2*2,4)==1
assert Fraction(0,2)-Fraction(2*2,4)==-1

# Universal but deliberately conservative complex-source zero-free radius.
# At fixed W: K/K0=1+s f+t g+st h, where f,g<=2 and h<=4.
r=S.Rational(9,100)
lower=S.factor(1-4*r-4*r*r)
assert lower==S.Rational(1519,2500)
assert lower>0

# Fail-closed detection: a spuriously coarse-factorized KFG need not
# agree with the original fine marks even if positivity of all four
# coefficients is retained. Do not mistake moment-cone membership
# for CMP119 physical same-source identification.
w=(1,1,1,1)
z=sum(w)
f=sum(v*a for v,(a,b) in zip(w,corners))
g=sum(v*b for v,(a,b) in zip(w,corners))
fg=sum(v*a*b for v,(a,b) in zip(w,corners))
assert fg==Fraction(f*g,z)  # this special example factorizes
bad_fg=Fraction(f*g,z)+1
assert 0<=bad_fg<=min(2*f,2*g)
assert bad_fg != fg
print(f"PASS {checked}/255 exact nonempty rational moment laws")
print("PASS sharp conditional covariance interval [-1,1] and PSD")
print("PASS original marked fibre |K(s,t)| >= (1519/2500) K0 for |s|,|t| <= 9/100")
print("PASS negative control: coefficient inequalities alone do not identify KFG")
print("NO CMP119 physical density/step identification, W3 rate or Clay claim")
