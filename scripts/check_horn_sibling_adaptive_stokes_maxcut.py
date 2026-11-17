#!/usr/bin/env python3
"""Hatcher sibling-adaptive holonomy bounds: exact arithmetic acceptance test.

Attribution: Hatcher AT Ex 2B.2 supplies marked commutator topology;
Gotô 1949 and neutrino PR #1247 already supply abstract SU3 representation
existence; horn PR #1244 supplies original geometry; hyperfabric PR #1249
supplies original 2^n and curved eta inequalities. THIS WORK adds the
sibling-sensitive coefficients and a curvature-area budget interface.

No actual marked horn loops, source curvature surfaces, physical experiment,
or theorem prover kernel check are constructed by this script.
"""
from fractions import Fraction as F

ROOT_GAP_SQ_LOWER=F(854996726408,648677790003)
assert ROOT_GAP_SQ_LOWER>1

def coefficient(sibling_gap):
    assert F(0)<=sibling_gap<=2
    return 2*min(F(1),sibling_gap)

def envelope(siblings, defects, leaf):
    assert len(siblings)==len(defects)
    assert leaf>=0 and all(e>=0 for e in defects)
    result=leaf
    for gap,error in reversed(list(zip(siblings,defects))):
        result=error+coefficient(gap)*result
    return result

def expanded(siblings, defects, leaf):
    prefix=F(1)
    total=F(0)
    for gap,error in zip(siblings,defects):
        total+=prefix*error
        prefix*=coefficient(gap)
    return total+prefix*leaf

for n in range(33):
    gaps=[min(F(2),F((7*k+2)%13,7+3*(k%4))) for k in range(n)]
    errors=[F((3*k+1)%7,1000+11*k) for k in range(n)]
    assert envelope(gaps,errors,F(2))==expanded(gaps,errors,F(2))
    assert envelope(gaps,errors,F(2)) <= (F(2)**n)*2 + sum((F(2)**k*e for k,e in enumerate(errors)),F(0))
print("PASS 33 exact heterogeneous sibling/defect identities and old-bound dominance")

# IMPORTANT: leaf gap is the universal d(U)<=2, NOT an assumed shrinking leaf.
# Sibling local loops shrink only at (3/4)^k; no q<1/2 hypothesis.
siblings=[F(3,4)**k for k in range(64)]
first=next(n for n in range(1,65) if envelope(siblings[:n],[F(0)]*n,F(2))<=1)
assert first==7
print("PASS flat sibling-only conditional no-go at depth",first)

# M=3 and unbased sibling lengths L=(1/3)(3/4)^k produce the
# stipulated gaps. Gauge-unitary whisker conjugation preserves d(U).
M=F(3)
local_lengths=[F(1,3)*F(3,4)**k for k in range(64)]
assert [min(F(2),M*x) for x in local_lengths]==siblings

# Curvature/homotopy: source must produce actual smooth BASED strips H_k.
# The non-Abelian variation bound is eta_k<=int ||F(H_s,H_t)|| dsdt;
# K=1/100 and synthetic area=(1/2)^k are illustrative, NOT source data.
K=F(1,100)
defects=[K*F(1,2)**k for k in range(64)]
curved=next(n for n in range(1,65) if envelope(siblings[:n],defects[:n],F(2))<=1)
assert curved==7
assert envelope(siblings[:curved],defects[:curved],F(2))<1
print("PASS conditional area-curvature budget at depth",curved)

# Negative controls: without sibling/curvature evidence no no-go follows.
for n in range(1,15):
    assert envelope([F(2)]*n,[F(0)]*n,F(2))==F(2)**(n+1)
assert envelope(siblings[:30],[F(2)]+[F(0)]*29,F(0))>=2
print("PASS fail-closed unlimited sibling and large root curvature controls")

# Exact SU3 sharpness matrix family of prior PR #1249; optional numerical check.
try:
    import numpy as np
    I=np.eye(3,dtype=complex)
    B=np.array([[0,1,0],[-1,0,0],[0,0,1]],dtype=complex)
    for n in (1,2,5,17,100):
        z=complex(n,1)/complex(n,-1)
        A=np.diag([z,1/z,1])
        C=A@B@A.conj().T@B.conj().T
        d=lambda Q:np.linalg.norm(Q-I,ord=2)
        assert d(C)<=2*d(A)+1e-12
        assert abs(d(C)**2/d(A)**2 - float(F(4*n*n,n*n+1)))<1e-9
    print("PASS SU3 norm-family controls")
except ImportError:
    print("SKIP optional numpy controls")
print("OPEN source-linked meridians, local sibling lengths, actual based Stokes surfaces")
