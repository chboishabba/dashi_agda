#!/usr/bin/env python3
"""Selected E6-derived orbifold 27: universal *index parity* criterion.

Original mathematical sources: Atiyah-Singer spin Dirac index, Chern-Weil
and classical E6 -> SU(3)^3 branching (Slansky 1981). Repository owners:
first-Tits/trinification Agda #1106; physical orbifold Agda #1241.
Source-written reduction: Johl Brown / OpenAI ChatGPT assistance.

The source H-equivariant 27 splits under orbifold parity. Its complete
Chern characters ch1, ch3 vanish, so on ANY closed spin six-manifold
with a faithful boundary-H bundle, the SIGNED index is even, provided
the stated equivariant splitting and standard spin Dirac index apply.
The program checks the polynomial trace identity and a nonliftable spin
(S2)^3 witness. It does NOT establish eta/torsion anomalies, global
5D CS/WZ levels, or all-field quantum gauge invariance.
"""
from itertools import product
from fractions import Fraction as F
import sympy as s

P=(-1,-1,1)
z=s.symbols("z0:18")
weights={}
for direction in range(3):
    for group in range(3):
        u,v=z[6*direction+2*group:6*direction+2*group+2]
        weights[group,direction]=(u,v,-u-v)

def char(block,i,j,d):
    c,l,r=[weights[k,d] for k in range(3)]
    return {"A":c[i]-l[j],"B":r[j]-c[i],
            "C":l[i]-r[j]}[block]

full=s.S.Zero
signed=s.S.Zero
linear_full=s.S.Zero
for block in "ABC":
    for i,j in product(range(3),repeat=2):
        h={"A":-P[j],"B":-P[j],"C":-P[i]*P[j]}[block]
        term=s.prod(char(block,i,j,d) for d in range(3))
        full+=term
        signed+=h*term
        linear_full+=char(block,i,j,0)
full=s.expand(full)
signed=s.expand(signed)
assert full==0 and s.expand(linear_full)==0
poly=s.Poly(signed,z)
assert poly.total_degree()==3 and len(poly.terms())>0
assert all(int(coef)%2==0 for _,coef in poly.terms())
assert s.expand(2*s.expand(signed/2)-signed)==0

# Nonliftable faithful H quotient over spin X=S2 x S2 x S2.
# Each S2 carries p=1 central deck clutch; the SU3 cover cannot
# close, yet each source 27-character line descends with INTEGER c1.
def lift(p,m,n):
    return (F(p,3)+m,F(p,3)+n,-F(2*p,3)-m-n)

def selected_indexes(config):
    W={(g,d):lift(*config[d][g]) for d in range(3) for g in range(3)}
    def q(block,i,j,d):
        c,l,r=[W[k,d] for k in range(3)]
        return {"A":c[i]-l[j],"B":r[j]-c[i],
                "C":l[i]-r[j]}[block]
    full_index=signed_index=F(0)
    for block in "ABC":
        for i,j in product(range(3),repeat=2):
            charges=[q(block,i,j,d) for d in range(3)]
            assert all(x.denominator==1 for x in charges)
            term=charges[0]*charges[1]*charges[2]
            full_index+=term
            signed_index+=({"A":-P[j],"B":-P[j],
                            "C":-P[i]*P[j]})[block]*term
    assert full_index==0 and signed_index.denominator==1
    assert signed_index.numerator%2==0
    return signed_index

base=[[(1,0,0)]*3 for _ in range(3)]
assert selected_indexes(base)==0
fixture=[[(1,1,0),(1,0,0),(1,0,0)],
         [(1,1,0),(1,0,0),(1,0,0)],
         [(1,0,0),(1,1,0),(1,0,0)]]
assert selected_indexes(fixture)==-12
print("PASS 27 source H-torus characters: ch1 and ch3 full traces vanish")
print("PASS",len(poly.terms()),"signed cubic terms, all even coefficients")
print("PASS nonliftable spin (S2)^3 signed index -12; half-index -6")
print("OPEN actual APS/eta, torsion, quantized 5D CS, patched WZ action")
