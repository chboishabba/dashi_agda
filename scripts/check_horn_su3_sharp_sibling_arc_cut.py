#!/usr/bin/env python3
"""Sharp spectral-arc sibling amplification certificate for SU(3)/unitaries.

ORIGINAL SOURCES: Hatcher, Algebraic Topology Ex 2B.2 owns horn commutator
marking; Goto 1949 owns compact semisimple commutator surjectivity;
Agda neutrino PR #1247 owns the selected W; Agda #1249 / Lean #84
own the earlier 2 min(1,delta) universal child multiplier.

NEW RESULT: When 0<=delta=||B-I||<=sqrt(2), choose the REAL scalar
lambda=1-delta**2/2 >=0. Unitarity and B+B*>=2lambda I give
||(B-lambda I)||**2 <= 1-lambda**2=delta**2-delta**4/4.
Since AB-BA=[A-I,B-lambda I],
  d([A,B])<=2 delta sqrt(1-delta**2/4) d(A).
This coefficient is SHARP among all SU(3) for a fixed delta in this
range, by B=diag(e^{ia},e^{-ia},1) and A_t=exp(it sigma_x) (+1).
The strict contraction threshold is sqrt(2-sqrt(3)) ~= .517638.
No geometry, actual horn meridians, field, or kernel proof is supplied.
"""
from fractions import Fraction as Q
from math import sqrt, sin, asin, cos

def sharp_coeff_sq(e):
    e = Q(e)
    assert 0 <= e <= 2
    if e*e >= 2:
        return Q(4)
    return 4*e*e*(1-e*e/4)

assert sharp_coeff_sq(Q(1,2)) == Q(15,16)
q=Q(31,60)
assert sharp_coeff_sq(q)==Q(12914879,12960000)
assert sharp_coeff_sq(q)<1
assert sharp_coeff_sq(Q(13,25))>1
assert Q(1,2)<q<Q(13,25)
assert Q(999,1000)**2>sharp_coeff_sq(q)
print('PASS exact Q(1/2) c^2=15/16 and Q(31/60) c^2=12914879/12960000 <1')

# Precise real threshold: e_*^2=2-sqrt(3), and
# 4 e^2(1-e^2/4)=1 exactly. Polynomial certificate.
from sympy import sqrt as symsqrt, simplify, S
threshold2=2-symsqrt(3)
assert simplify(4*threshold2*(1-threshold2/4)-1)==0
assert 0<float(threshold2)<2
print('PASS symbolic critical delta^2=2-sqrt(3)')

# The resulting product is a NORM-SQUARED bound, avoiding floating
# eigenvalues even at very large finite depths.
for e, expected in [(Q(1,2),22),(q,398)]:
    c2=sharp_coeff_sq(e)
    p=Q(1);n=0
    while 4*p>1:
        p*=c2;n+=1
    assert n==expected and 4*p<=1 and 4*p/c2>1
    print('PASS exact squared-gap finite contradiction for uniform sibling gap',e,'depth',n)

# Realized sharpness (this is an independent NUMERICAL sanity check,
# not a substitute for the displayed algebraic 3x3 proof).
try:
    import numpy as np
    I=np.eye(3,dtype=complex)
    for e in (Q(1,4),Q(1,2),q,Q(1),Q(7,5)):
        delta=float(e)
        a=2*asin(delta/2)
        z=complex(cos(a),sin(a))
        B=np.diag([z,z.conjugate(),1])
        measured_delta=np.linalg.norm(B-I,ord=2)
        assert abs(measured_delta-delta)<1e-12
        for t in (0.01,0.0001):
            A=np.array([[cos(t),1j*sin(t),0],[1j*sin(t),cos(t),0],[0,0,1]],dtype=complex)
            comm=A@B@A.conj().T@B.conj().T
            ratio=np.linalg.norm(comm-I,ord=2)/np.linalg.norm(A-I,ord=2)
            upper=sqrt(float(sharp_coeff_sq(e)))
            assert ratio <= upper+1e-10
            assert abs(ratio-2*sin(a)*cos(t/2)) <1e-9
            if t==0.0001: assert upper-ratio<1e-8
    print('PASS SU3 explicit sharpness matrices across five rational gaps')
except ImportError:
    print('SKIP optional numpy matrix confirmation')

# Curved-interface conservative RATIONAL cap: gap<=31/60 implies
# local sharp amplification <=999/1000 (squared check above).
# Parent-to-word defects eta_k supplied by genuine source surfaces.
# Synthetic example with flat or tiny defects demonstrates contraction
# where the PRIOR coefficient 2*gap=31/30 >1 could not.
a=Q(999,1000)
N=1400
leaf=Q(2)
eta=Q(1,1000000)
out=leaf
for _ in range(N):
    out=eta+a*out
assert out<1
old=Q(2)*(2*q)**30
assert old>2
print('PASS new rational curved source budget with a=999/1000, eta=1e-6, n=1400; old local factor>1')

# Negative control: without actual source-marked sibling gaps this
# abstract coefficient cannot reject ANY selected physical W.
assert sharp_coeff_sq(Q(2)) == 4
print('PASS fail-closed large gap c=2; SOURCE loops/curvature still open')
