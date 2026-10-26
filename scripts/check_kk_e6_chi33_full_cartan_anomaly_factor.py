#!/usr/bin/env python3
"""Full rank-six Cartan factorization through SAME Chi33 line character.

Source: actual 27=(3c,bar3L,1)+(bar3c,1,3R)+(1,3L,bar3R),
selected orbifold intrinsic parity from Agda E6 #1106 and KK #1241.
Original prior art: classical Chern-Weil / Atiyah-Singer spin index,
orbifold anomaly descent (Scrucca et al 2002; von Gersdorff &
Quirós 2003), global WZW via invertible field theories (Yonekura 2021).
The factored selected-source polynomial is a repo calculation,
Johl Brown with OpenAI ChatGPT-assisted implementation.

Rational cohomology statement (standard splitting principle):
  signed ch_1(Eplus-Eminus) = 8 D
  signed tr(F^3) = 4 D Q
  signed ch_3 = (2/3) D Q
  spin six-index density = D * (2 Q/3 - p1(TX)/3),
where D=c1(L_Chi33)=l3-r3. This is a source Chern-character
identity, not a quantum determinant/eta or global WZ/CS action.
In particular, if D=0 in rational H2, the *free index* vanishes.
Conversely a NONZERO signed spin index forces D nonzero rationally
and consequently forbids a nowhere-zero Chi33 section.
Torsion eta may survive even if D=0, so do not promote to total
anomaly vanishing.
"""
from itertools import product
import sympy as s

c0,c1,l0,l1,r0,r1=s.symbols("c0 c1 l0 l1 r0 r1")
p1=s.symbols("p1")
c=(c0,c1,-c0-c1)
l=(l0,l1,-l0-l1)
r=(r0,r1,-r0-r1)
P=(-1,-1,1)
D=s.expand(l[2]-r[2])
Q=s.expand(3*(c0*c0+c0*c1+c1*c1)
    +2*(l0*l0+l1*l1+r0*r0+r1*r1)
    +l0*l1+r0*r1+2*(l0+l1)*(r0+r1))

linear=cubic=s.S.Zero
full_linear=full_cubic=s.S.Zero
for block in "ABC":
    for i,j in product(range(3),repeat=2):
        h={"A":-P[j],"B":-P[j],"C":-P[i]*P[j]}[block]
        q={"A":c[i]-l[j],"B":r[j]-c[i],"C":l[i]-r[j]}[block]
        linear+=h*q
        cubic+=h*q**3
        full_linear+=q
        full_cubic+=q**3
linear=s.expand(linear)
cubic=s.expand(cubic)
assert s.expand(full_linear)==s.expand(full_cubic)==0
assert s.expand(linear-8*D)==0
assert s.expand(cubic-4*D*Q)==0
six_index_density=s.expand(cubic/s.Integer(6)-p1*linear/s.Integer(24))
assert s.expand(six_index_density-D*(s.Rational(2,3)*Q-p1/s.Integer(3)))==0
# Full even boundary group Weyl action: c S3, L S2, R S2.
# Test permutations of all three colour roots and exchange doublet roots.
def swap_colour(poly, permutation):
    temp=s.symbols("tmp0:3")
    old=(c0,c1)
    # Weyl permutations are tested via simultaneous symbolic substitution
    subs={c0:c[permutation[0]],c1:c[permutation[1]]}
    return s.expand(poly.subs(subs, simultaneous=True))
for permutation in product(range(3),repeat=3):
    if len(set(permutation))==3:
        assert s.expand(swap_colour(Q,permutation)-Q)==0
assert s.expand(Q.subs({l0:l1,l1:l0},simultaneous=True)-Q)==0
assert s.expand(Q.subs({r0:r1,r1:r0},simultaneous=True)-Q)==0
assert s.expand(D.subs({l0:l1,l1:l0},simultaneous=True)-D)==0
assert s.expand(D.subs({r0:r1,r1:r0},simultaneous=True)-D)==0
# Key negative control: free index = 0 if Chi line class is 0,
# but this proves nothing about torsion/global eta.
assert s.expand(six_index_density.subs(r1,l0+l1-r0))==0
assert s.expand(Q.subs(r1,l0+l1-r0))!=0  # nontrivial 4-form factor
print("PASS full SU3c x U2L x U2R Cartan trace factorization")
print("PASS source chi33 character D =",D)
print("PASS signed ch1=8D; signed trF^3=4D Q with Q =",Q)
print("PASS six-spin-index density D*(2 Q/3 - p1/3)")
print("PASS H Weyl invariance: S3 colour x S2L x S2R")
print("PASS D=0 kills free anomaly index, NOT possible torsion eta")
print("OPEN integral differential refinement / spin CS and forced-zero WZ completion")
