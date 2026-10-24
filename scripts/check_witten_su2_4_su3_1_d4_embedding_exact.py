#!/usr/bin/env python3
"""Exact conformal embedding SU(2)_4 -> SU(3)_1 and D4 modular invariant.

PRIOR ART: J. Lacki and Ph. Zaugg (1989), Phys. Lett. B228, 223-227
DOI 10.1016/0370-2693(89)90662-X; Cappelli, Itzykson & Zuber (1987);
standard affine/WZW conformal embeddings and simple-current extension.
EXISTING DASHI OWNERS: SU2Level4Spin1RepReceipt,
SU3FromAnyon3FoldReceipt, LevelRankDualityReceipt,
BulkBoundarySU3Receipt, Monster/AdS3 sibling PR #1239.
All matrix identities here are algebraic in Q(sqrt(3), omega).
No construction of affine currents, Q-system, braided VOA,
CS path integral, physical SU3_c, Monster, or C27 realization.
"""
from itertools import product
from fractions import Fraction as F
from sympy import Matrix, eye, sqrt, sin, pi, I, simplify, conjugate

K=4
omega=(-1+I*sqrt(3))/2
S2=Matrix(5,5,lambda a,b:simplify(sin(pi*(a+1)*(b+1)/6)/sqrt(3)))
S3=Matrix(3,3,lambda a,b:simplify(omega**(a*b)/sqrt(3)))
# SU3_1 vacuum -> SU2_4 (0)+(4). Two different SU3 fundamental
# modules have the SAME restricted SU2_4 sector (2); DO NOT merge them.
B=Matrix([[1,0,0,0,1],
          [0,0,1,0,0],
          [0,0,1,0,0]])
D4=B.T*B
def exact_zero(M):
    return all(simplify(v)==0 for v in M)
assert exact_zero(S2*S2-eye(5))
charge_conjugation=Matrix([[1,0,0],[0,0,1],[0,1,0]])
assert exact_zero(S3*S3-charge_conjugation)
assert exact_zero(B*S2-S3*B)
assert exact_zero(S2*D4-D4*S2)
assert D4==Matrix([[1,0,0,0,1],[0,0,0,0,0],
                    [0,0,2,0,0],[0,0,0,0,0],
                    [1,0,0,0,1]])
print("PASS exact SU2_4 -> SU3_1 branching BS2=S3B and D4 modular S invariance")

h2=[F(a*(a+2),24) for a in range(5)]
h3=[F(0),F(1,3),F(1,3)]
assert h2==[F(0),F(1,8),F(1,3),F(5,8),F(1)]
for a,b in product(range(3),range(5)):
    if B[a,b]:
        assert (h3[a]-h2[b]).denominator==1,(a,b)
for a,b in product(range(5),repeat=2):
    if D4[a,b]:
        assert (h2[a]-h2[b]).denominator==1,(a,b)
assert 3*K/(K+2)==2
assert F(1*8,1+3)==2 # c(su3_1)=k dim(g)/(k+g)=8/4
print("PASS exact D4 T-phase consistency, c_SU2_4=c_SU3_1=2, j4 boson h4=1")
# In literature: Z_D4=abs(chi0+chi4)^2 + 2 abs(chi2)^2
assert D4[0,4]==D4[4,0]==1 and D4[2,2]==2

# SU3_1 affine Verlinde with three simple objects fusing as C3.
fusion={}
for a,b,c in product(range(3),repeat=3):
    got=simplify(sum(
        S3[a,x]*S3[b,x]*conjugate(S3[c,x])/S3[0,x]
        for x in range(3)))
    target=int((a+b-c)%3==0)
    assert got==target,(a,b,c,got,target)
    fusion[a,b,c]=target
for a,b,c,d in product(range(3),repeat=4):
    assert sum(fusion[a,b,x]*fusion[x,c,d] for x in range(3))==sum(
        fusion[b,c,x]*fusion[a,x,d] for x in range(3))
assert all(simplify(S3[0,a]/S3[0,0]-1)==0 for a in range(3))
print("PASS 27 exact SU3_1 Verlinde coefficients C3 and 81 associativity checks")
# The extended pointed SU3_1 category has quantum dimensions 1,1,1
# and spins (1,omega,omega). Its Gauss-Milgram phase equals the
# source SU2_4 phase i; matching *framing* is required for a local
# bosonic extension, not a Monster c24 equivalence (phase 1).
framing_SU3=simplify((1+2*omega)/sqrt(3))
assert framing_SU3==I
print("PASS exact SU3_1 framing phase i = SU2_4 phase i; not Monster c24 phase 1")

# SU2_4 simple currents only 0 and 4 (d=1). In the EXTENDED SU3_1
# there are 0,1,2 invertible sectors, after resolution of j=1 fixed point.
dimensions=[simplify(S2[0,a]/S2[0,0]) for a in range(5)]
assert dimensions==[1,sqrt(3),2,sqrt(3),1]
assert [a for a,d in enumerate(dimensions) if d==1]==[0,4]
for a in range(5):
    targets=[c for c in range(5) if
      (4+a+c)%2==0 and abs(4-a)<=c<=min(4+a,8-4-a)]
    assert targets==[4-a]
print("PASS SU2_4 invertibles Z2={0,4}; bosonic j4 fixes sector2, which splits in SU3_1")
print("NO-GO direct C3 simple-current action in unextended SU2_4; constructive C3 after source extension")
print("BOUNDARY C3 SU3_1 fusion != horned-geometric C3 or Monster C27; no physical colour gauge promotion")
