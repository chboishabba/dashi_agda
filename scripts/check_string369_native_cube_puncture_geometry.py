#!/usr/bin/env python3
"""Native ternary cube C3 puncture and selected Jacobian transport.
Classical: cube body-diagonal rotation, permutation representations.
Original DASHI: Punctured27NineSheetBridgeExact, OggSSPP2BalancedTernaryPuncturedPlaneExact,
TrialecticT18CyclicBoundaryActionExact, selected Tian-Yau Jacobian.
User: geometric explanation of three punctured sheets.
New: remove a cyclic orbit transversal to horizontal sheets, not the fixed axis.
"""
from itertools import product
from pathlib import Path
import runpy
import sympy as s
T=(-1,0,1)
cube=set(product(T,repeat=3))
def g(p):return (p[1],p[2],p[0])
hole=(-1,0,1)
holes={hole,g(hole),g(g(hole))}
W=cube-holes
assert len(W)==24 and {g(p) for p in W}==W
fixed=sorted(p for p in W if g(p)==p)
assert fixed==[(-1,-1,-1),(0,0,0),(1,1,1)]
orbits=sorted({tuple(sorted((p,g(p),g(g(p))))) for p in W if g(p)!=p})
assert len(orbits)==7 and all(len(o)==3 for o in orbits)
# Horizontal sheet has exactly one missing site. Translate in F3^2
# to recenter each puncture. This is a finite chart reindexing, NOT
# Euclidean translation/rotation about the sheet centre.
def trit(a):return (a+1)%3-1
centres={z:(x,y) for x,y,z in holes}
def chart(p):
    x,y,z=p;a,b=centres[z]
    return (trit(x-a),trit(y-b),z)
def unchart(p):
    x,y,z=p;a,b=centres[z]
    return (trit(x+a),trit(y+b),z)
assert {chart(p) for p in W}=={(x,y,z) for x,y,z in cube if (x,y)!=(0,0)}
assert all(unchart(chart(p))==p for p in W)
assert all(sum(p[2]==z for p in W)==8 for z in T)
# Native same-centre removal is instead removing z axis, not C3 stable.
axis={(0,0,z) for z in T}
assert {g(p) for p in axis}!=axis
# Basis indexed by actual cycles then fixed sites.
order=[]
for o in orbits:
    p=o[0];order.extend([p,g(p),g(g(p))])
order.extend(fixed)
P=s.zeros(24)
for i,p in enumerate(order):P[order.index(g(p)),i]=1
assert P**3==s.eye(24) and P.trace()==3
assert ((s.eye(24)+P+P**2)/3).rank()==10
# Native permutation descends after removal of any one FIXED basis line.
assert P[:23,:23].trace()==2
print('PASS native cube rotation, 3 fixed sites and 7 cyclic triples')
print('PASS three punctured charts, exact modular recentering')
# Optional integration (previous checker must run to completion).
if __name__=='__main__':
    import sys
    if '--jacobian' in sys.argv:
        d=runpy.run_path(str(Path(__file__).with_name(
            'check_string369_tian_yau_punctured_sheet_tensor_codec.py')))
        J=d['S2'];P2=d['P2'];K=d['K'][0];B=d['B']
        assert P2*J==J*P and J[:,21]==K
        assert B*J[:,21]==s.zeros(23,1)
        print('PASS actual Jacobian transport; designated fixed site maps to radical')
# No canonical choice of radical site, ring product or physical fibration
# follows solely from the permutation representation.
