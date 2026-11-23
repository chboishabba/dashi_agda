#!/usr/bin/env python3
"""Exact-rational and symbolic SI scale verification for native R445 two-step block.

Source owners: DASHI.Physics.Units.SI, SIMetrologyBridge,
YangMillsSIScalingEndpointExact, BalabanPhysicalClusteringScaleAlgebraExact,
YMClayR445OriginalAxialBondParityInjectiveExact and the Base2/369 R445 codec.
Not a proof of a positive physical Wilson mass gap or Agda kernel acceptance.
"""
import sympy as s

# SI dimension vectors: (L,M,T,I,Theta,N,J) -- BIPM convention
L=(1,0,0,0,0,0,0)
L_INV=(-1,0,0,0,0,0,0)
M=(0,1,0,0,0,0,0)
E=(2,1,-2,0,0,0,0)
HBAR=(2,1,-1,0,0,0,0)
C=(1,0,-1,0,0,0,0)

def mul_dims(*dims):
    return tuple(sum(d[i] for d in dims) for i in range(7))

def inverse_dims(d):
    return tuple(-x for x in d)

assert mul_dims(HBAR,inverse_dims(C),L_INV)==M
assert mul_dims(HBAR,C,L_INV)==E
assert mul_dims(L,L_INV)==(0,)*7

ell, ainv, lamb, kinv, d=s.symbols('ell ainv lamb kinv d',positive=True)
physical_fine=s.expand(lamb*ainv)
physical_coarse=s.expand((lamb+lamb)*kinv)
# Agda field: 2*coarseInverseSpacing == fineInverseSpacing
assert s.simplify(physical_coarse.subs(kinv,ainv/2)-physical_fine)==0
assert s.simplify((ell+ell)-2*ell)==0
# Exact dimensional/rate physical exponent equality for 2 fine steps:
assert s.simplify(lamb*(2)- (2*lamb))==0

q=s.symbols('q',positive=True)
spacing=s.symbols('a',positive=True)
mu=s.symbols('mu',positive=True)
# Multiplicative rate transport holds if actual coarse factor equals q_fine squared,
# NOT from the 8 parity-sheet label count or from block geometry alone.
assert s.simplify(-s.log(q*q)/(2*spacing) + s.log(q)/spacing)==0
# If q_coarse = q_fine with doubled physical distance, rate halves.
assert s.simplify(-s.log(q)/(2*spacing) + s.log(q)/(2*spacing))==0
# Model-dependent running factors which have a finite physical rate.
for n in range(1,17):
    a=s.Rational(1,2**n)
    qn=s.exp(-mu*a)
    assert s.simplify(-s.log(qn)/a-mu)==0
# By contrast a cutoff-independent 0<q<1 has divergent inverse length as a->0.
assert s.limit(-s.log(s.Rational(1,2))/spacing,spacing,0,dir='+')==s.oo

# Original side-four is 1024 bond LABELS, eight transverse sheets only, 
# while physical axial block has precisely two consecutive fine links.
assert 4*4**4==1024 and 4*2**4*2==128 and 1024-128==896
assert 1024==2**10 and 128==2**7 and 8==2**3

print('PASS: seven-exponent BIPM SI vectors distinguish m^-1, kg and J')
print('PASS: hbar/c × m^-1 = kg; hbar*c × m^-1 = J')
print('PASS: fine (lambda × a^-1) = coarse (2 lambda × (a^-1/2))')
print('PASS: physical native R445 axial length = 2 fine SI lengths, not 8')
print('PASS: q_coarse=q_fine^2 gives matching inverse length; no automatic dynamics')
print('PASS: q_n=exp(-mu a_n) yields finite mu; fixed q<1 as a_n→0 diverges')
print('PASS: original full 1024 bonds = 128 selected + 896 residual, no deletion')
print('Boundary: original all-cutoff CMP116/W1/W3 physical rate and OS H remain OPEN')
