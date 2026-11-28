"""Rational SU(2) carrier is not closed under 13th roots even near identity.
The proof is for the constant commuting sector, not the unrestricted
regular-gauge variational minimizer. Exact arithmetic checks the witness.
"""
from fractions import Fraction as F
from math import gcd
import sympy as S
m=32768;d=m*m+1;a=m*m-1;b=2*m
assert a*a+b*b==d*d and gcd(a,b,d)==1
assert F((a-d)**2+b*b,d*d)<=4*F(1,8192)**2
assert 4**13<d<5**13
# A primitive rational complex unit (A+iB)/D has odd denominator D.
# For p|D, A and B cannot vanish mod p; (A+iB)^2=2A(A+iB) mod p.
# Consequently no p|D cancels in BOTH integer coordinates of its power,
# and the reduced common denominator after power 13 is exactly D**13.
A,B=S.symbols('A B',real=True);i=S.I;z=A+i*B
assert S.expand(z*z-2*A*z)==-(A*A+B*B)
# An arbitrary quaternion root of q commutes with q; nonzero imaginary part
# of q forces its root to share that axis. Thus no rational quaternion root.
print('PASS primitive unit q=',F(a,d),F(b,d),'chord squared=',F((a-d)**2+b*b,d*d))
print('PASS denominator',d,'strictly between 4^13 and 5^13; rational 13th root impossible')
