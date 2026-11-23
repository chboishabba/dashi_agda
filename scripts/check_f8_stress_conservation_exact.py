"""Finite exact cross-lane stress regression; no physical source or experiment.
Reuse CMP119AntigravityTraceVsActiveStressFirewallExact and
SameObjectConservationLedgerExact. Standard Lorentzian stress algebra;
Brown--Maclay ideal plate tensor is a theory fixture, not total apparatus.
"""
from fractions import Fraction as F
from itertools import product
import sympy as s
r, x, y, z, dr, dt = s.symbols('rho px py pz dr dt', real=True)
tau = -r+x+y+z
active = r+x+y+z
assert s.expand(active-tau-2*r)==0
assert s.expand((tau+dt+2*(r+dr))-active)==dt+2*dr
# Exact rectangular uncertainty hull, including both attainable extremes.
count=0
for rh, th, er, et in product(range(-2,3),range(-3,4),[F(0),F(1,4),F(1)], [F(0),F(1,3),F(1)]):
    lo,hi=th+2*rh-et-2*er,th+2*rh+et+2*er
    vals=[th+v*et+2*(rh+w*er) for v,w in product([-1,0,1],repeat=2)]
    assert min(vals)==lo and max(vals)==hi
    assert not (hi<0) or all(a<0 for a in vals)
    assert not (lo>0) or all(a>0 for a in vals)
    count+=len(vals)
# Same trace, opposite active sign; trace alone cannot decide.
assert -1+0+0+0 == -3+2+0+0 == -1
# Choose same negative trace -2, densities 0 and 2.
assert -2+2*0<0<-2+2*2
# Ideal EM plate stress in units with positive scale C=1: rho=-1,
# transverse p=+1, normal p=-3. Trace zero, active=-2.
assert -(-1)+1+1-3==0 and -1+1+1-3==-2
# An isolated static closed source must include support stresses.
# Illustrative algebraic cancellation, not a physical plate support model.
assert (1+1-3)+(-1-1+3)==0
# Signed accounting: observed = admitted + newly admitted + residual.
a,b,c=s.symbols('observed accounted nuisance')
assert s.expand((a-b-c)-(a-b)+c)==0
# The same finite interval cannot be declared closed with an unknown nuisance.
print(f'PASS {count} exact rational interval checks; symbolic trace and signed residual; ideal plate and trace negative controls')
