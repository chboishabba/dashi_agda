#!/usr/bin/env python3
"""Global-test-family check for selected E6-derived orbifold 27 parity anomaly.

Original source: 27 under gauged SU3c x SU3L x SU3R, with
P_c=I and P_L=P_R=diag(-,-,+), owner E6 #1106, KK #1241.
Original mathematics: Atiyah-Singer Dirac index and spin A-hat genus,
not a discovery of this repo. Original GS/orbifold physics:
von Gersdorff/Quiros PRD68 (2003)105002.

On spin CP^3, p1=4h²; for 6D Weyl fermion charge q with
U1 line bundle c1=q*h, index=(q³-q)/6. Summing left-minus-right
zero modes of full 27 gives
I(m,n)=(m-n)*(40m²+64mn+40n²-16)/6
      = 4/3*(m-n)*(5m²+8mn+5n²-2).
For ALL integral m,n the index is EVEN. Proof: the product of
(m-n) with bracket is divisible by 3; a 9-case residue check
establishes this modulo 3. This is a real spin background family
and stronger than naive integer source-trace coefficients.

S² x S⁴ with one SU3c or SU2L/R instanton and U1 flux:
mixed local index coefficient (actual fund index normalization)
4(m-n)*k, even. S² x K3 gives gravitational index 2*16(m-n),
also even. Still NOT a full spin bordism/global quotient/APS eta
theorem; true SU3^3 quotient lattice and CS counterterms are OPEN.
"""
from fractions import Fraction as F
from itertools import product
import sympy as s
P=(-1,-1,1); UL=(-1,-1,2);UR=(-1,-1,2)
rows=[]
for c,l in product(range(3),repeat=2):
    rows.append(dict(h=-P[l],ql=-UL[l],qr=0,rep="c",L=l,R=None))
for c,r in product(range(3),repeat=2):
    rows.append(dict(h=-P[r],ql=0,qr=UR[r],rep="barc",L=None,R=r))
for l,r in product(range(3),repeat=2):
    rows.append(dict(h=-P[l]*P[r],ql=UL[l],qr=-UR[r],rep="1",L=l,R=r))
assert len(rows)==27
x,y=s.symbols("m n",integer=True)
qsum=lambda pow: s.expand(sum(a["h"]*(a["ql"]*x+a["qr"]*y)**pow for a in rows))
cub=qsum(3);linear=qsum(1)
assert s.expand(cub-(x-y)*(40*x*x+64*x*y+40*y*y))==0
assert linear==16*(x-y)
index=s.factor((cub-linear)/6)
assert s.simplify(index-(x-y)*(40*x*x+64*x*y+40*y*y-16)/6)==0

# MOD-3 COMPLETE. Since 5m²+8mn+5n²-2 ≡
# 2(m-n)²+1 (mod3), and (m-n) ∈ {0,1,2}, their
# product is 0 in all nine residue pairs.
for m,n in product(range(3),repeat=2):
    assert ((m-n)*(5*m*m+8*m*n+5*n*n-2))%3==0
for m,n in product(range(-15,16),repeat=2):
    q=F((m-n)*(40*m*m+64*m*n+40*n*n-16),6)
    assert q.denominator==1 and q.numerator%2==0

# Normalize non-Abelian instanton with an SU3 or SU2
# fundamental Weyl index equal to one. Divide by representation
# multiplicity 3 (colour) or 2 (doublet), respectively.
def mixed_index(gauge):
    subset={
       "c": lambda a:a["rep"] in ("c","barc"),
       "L": lambda a:a["L"] is not None and a["L"]<2,
       "R": lambda a:a["R"] is not None and a["R"]<2
    }[gauge]
    dim={"c":3,"L":2,"R":2}[gauge]
    return s.expand(sum(a["h"]*(a["ql"]*x+a["qr"]*y)
                        for a in rows if subset(a))/dim)
for g in ("c","L","R"):
    assert mixed_index(g)==4*(x-y),(g,mixed_index(g))
# Gravitational spin K3 index Â(K3)=2:
assert s.expand(2*linear)==32*(x-y)
print("PASS CP3 spin U1L/U1R index:",index)
print("PASS complete mod3 proof: CP3 source index divisible by TWO for all integer m,n")
print("PASS spin S2xS4 SU3c/SU2L/SU2R unit-instanton families, index=4(m-n) each")
print("PASS spin S2xK3 gravitational family, index=32(m-n)")
print("OPEN spin bordism completeness, full quotient-gauge bundles, torsion/anomaly eta, true 5D CS/WZ action")
