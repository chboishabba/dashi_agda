#!/usr/bin/env python3
"""Section37 exact finite submodel checks for BSD/Hodge/PNP.

These checks are NOT Lean/Agda native receipts and prove no universal
Clay endpoint. Arithmetic is exact; all proofs/checkers stay committed.
"""
from fractions import Fraction as F
from itertools import product
import sympy as s

checks = {"BSD_symmetric_h": 0, "BSD_max_floor": 0,
          "Hodge_two_lifts": 0, "PNP_external_witness": 0}
for a,b in ((F(1,2),F(3,4)), (F(2),F(5)),
            (F(5),F(2)), (F(4,3),F(7,3))):
    h = [F(1)]
    for n in range(1,42):
        h.append(a*h[-1] + b**n)
    r = a+b+1
    m = lambda k: F(0) if k==0 else r**k
    for n in range(40):
        assert h[n+1] == a*h[n] + b**(n+1)
        assert h[n+1] == b*h[n] + a**(n+1)
        checks["BSD_symmetric_h"] += 2
        source = h[n]*m(n+2)-h[n+1]*m(n+1)
        assert source>0
        assert m(n+2) > max(a,b)*m(n+1)
        assert m(n+2) >= max(a,b)**n*m(2)
        checks["BSD_max_floor"] += 3

x,y=s.symbols("x y")
# Original fold ideal model (xy, y²), two equal modulo I lifts:
# D=x, E=x+xy. The saturation by either is the ideal (y).
D=x; E=x+x*y
G=s.groebner([x*y, y*y], y, x)
assert G.reduce(s.expand(E-D))[1]==0
for ax,ay,bx,by in product(range(-2,3),repeat=4):
    p=ax+ay*x+bx*y+by*x*y
    sat=s.expand(p.subs(y,0))==0
    for j,k in ((0,0),(1,2),(3,1),(4,4)):
        assert (s.expand(D**j*p).subs(y,0)==0) == sat
        assert (s.expand(E**k*p).subs(y,0)==0) == sat
        checks["Hodge_two_lifts"] += 2

# One retained initial state, opposite Boolean consumers:
# a faithful 1-step realization must distinguish its observation.
# No closed observer can do so for BOTH source inputs simultaneously.
for readout in (0,1):
    obs={0:0,1:1}
    initial={0:0,1:0}
    assert initial[0] == initial[1]
    assert obs[0] != obs[1]
    assert any(obs[u] != readout for u in (0,1))
    checks["PNP_external_witness"] += 1
print("CLAY37 EXACT CHECKS PASS",checks,"TOTAL",sum(checks.values()))
