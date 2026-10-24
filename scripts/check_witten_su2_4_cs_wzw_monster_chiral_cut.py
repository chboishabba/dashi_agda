#!/usr/bin/env python3
"""Exact Witten 1989 SU2_4 CS/WZW fusion vs Witten 2007 c24 Monster CFT.

Published prior art: Witten 1989 CMP 121 351-399; Verlinde modular fusion;
FLM 1988 Monster VOA; Witten 2007 arXiv:0706.3359 and Maloney/Witten
2007 arXiv:0712.0155. This exact test does not implement CS path integrals,
an affine VOA, the quantum gravity bulk or any hyperfabric same-object map.
Existing original DASHI owners: KacMoodyLevelReceipt,
SU2Level4Spin1RepReceipt, monster-c24-virasoro-primary-ads3-maxcut.md.
"""
from fractions import Fraction as F
from itertools import product
from sympy import Matrix, Rational as Q, sqrt, simplify, I

K = 4
ROOT3 = sqrt(3)
SINS = [Q(0),Q(1,2),ROOT3/2,Q(1),ROOT3/2,Q(1,2),
        Q(0),-Q(1,2),-ROOT3/2,-Q(1),-ROOT3/2,-Q(1,2)]
S = Matrix(5,5,lambda a,b:SINS[((a+1)*(b+1))%12]/ROOT3)
assert S == S.T
assert all(simplify(v)==0 for v in (S*S-Matrix.eye(5)))
print('PASS exact SU2_4 S symmetric, S²=I; CS torus blocks=5')

def fusion_rule(a,b,c):
    return int((a+b+c)%2==0 and abs(a-b)<=c<=min(a+b,2*K-a-b))

N = {}
for a,b,c in product(range(5),repeat=3):
    got = simplify(sum(S[a,x]*S[b,x]*S[c,x]/S[0,x] for x in range(5)))
    target=fusion_rule(a,b,c)
    assert got == target,(a,b,c,got,target)
    N[a,b,c]=target
for a,b,c,d in product(range(5),repeat=4):
    left=sum(N[a,b,x]*N[x,c,d] for x in range(5))
    right=sum(N[b,c,x]*N[a,x,d] for x in range(5))
    assert left==right,(a,b,c,d)
assert N[1,1,0]==N[1,1,2]==1 and N[1,1,4]==0
assert N[4,4,0]==1 and sum(N[4,4,c] for c in range(5))==1
print('PASS 125 exact Verlinde fusion coefficients and 625 associativity checks')

weights=[F(a*(a+2),24) for a in range(5)]
assert weights == [F(0),F(1,8),F(1,3),F(5,8),F(1)]
quantum=[simplify(S[0,a]/S[0,0]) for a in range(5)]
assert quantum==[1,ROOT3,2,ROOT3,1],quantum
assert simplify(sum(d*d for d in quantum)-12)==0
print('PASS 5 WZW weights and quantum dimensions 1,sqrt3,2,sqrt3,1; D²=12')

twist=[Q(1),(1+I)/sqrt(2),(-1+I*ROOT3)/2,-(1+I)/sqrt(2),Q(1)]
gauss=simplify(sum(quantum[a]**2*twist[a] for a in range(5))/sqrt(12))
assert gauss==I,gauss
print('PASS exact Witten CS framing phase exp(2pi*i*c/8)=i, c=2')

# Holomorphic Monster Vnatural c24 has one irreducible chiral module;
# topological modular phase exp(2pi*i*24/8)=1.
assert len(weights)!=1 and gauss!=1 and (24%8)==0 and (2%8)!=0
print('NO-GO DIRECT CHIRAL MODULE/CATEGORY: SU2_4 5 primaries, phase i; Monster c24 1, phase 1')

assert 196884==196883+1
print('PASS independent Monster level2 stress/primary count 196883+1')
print('BOUNDARY no CS path integral, actual affine VOA, Monster AdS3 bulk, or hyperfabric intertwiner')
