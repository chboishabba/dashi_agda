#!/usr/bin/env python3
"""E6 first-Tits diagonal Z3 quotient: mixed PSU3 fractional instanton test.

Original group: PR #1106 first-Tits 27 central kernel Z3_diag;
global-form identification and orbifold parity-even S2 clutch PR #1241.
For G=(SU3c×SU3L×SU3R)/Z3_diag, all three projected PSU3 bundles
inherit the SAME lifting obstruction B in H²(X,Z3).

Original fractional instanton relation (standard PSU(N) normalization):
I(PSU3) mod1 = ((3-1)/(2*3)) int P(B) = (1/3) int B∪B mod1
for odd N=3 (P(B)=B² mod3). On spin oriented 4-folds it can be
0,1/3,2/3. The three fractions EQUAL due to shared B; therefore
I_c+I_L+I_R is INTEGER modulo one. The SOURCE SELECTED WZ X4/2
has EQUAL mixed coefficients 1*(c2c+c2L+c2R) in its NAIVE
integer trace normalization. Thus diagonal Z3 fractional
instanton alone does not obstruct THIS particular equal-weight
combination. Single weighted c2c would fail for B²=2 mod3.

Concrete spin X=S²×S², B=u+v, u²=v²=0, uv=1:
B²=2uv -> projected fractions 2/3 each, sum=2.
This is a necessary MIXED sector test only. Full physically
normalized mixed coefficients, Abelian bundle-c1 constraints,
spin torsion/eta, global CS, WZ Higgs periodicity, and 5D
source action remain open. Source science: PSU3 fractional
instanton/Pontryagin-square literature, not our discovery.
"""
from fractions import Fraction as F

for pontryagin_mod3 in (0,1,2):
    fractional=F(pontryagin_mod3,3)
    projected=[fractional]*3
    combined=sum(projected,F(0))
    assert combined.denominator==1
    if pontryagin_mod3:
        assert projected[0].denominator==3
    print("B^2 mod3",pontryagin_mod3,
          "projected PSU3 fractional instantons",projected,
          "equal-weight mixed WZ combination",combined)
# Actual spin S2xS2 with B=u+v in mod3 cohomology.
u2,v2,uv=0,0,1
Bsq=(u2+2*uv+v2)%3
assert Bsq==2 and sum((F(Bsq,3) for _ in range(3)),F(0))==2
# A source with just one SU3c contribution fails on same background.
assert F(Bsq,3).denominator==3
# Only equal weights modulo 3 cancel the common fractional part.
for weights in ((1,1,1),(4,4,4),(1,0,0),(1,1,0)):
    net=sum((weights[i]*F(Bsq,3) for i in range(3)),F(0))
    assert (net.denominator==1)==(sum(weights)%3==0)
print("PASS diagonal Z3 mixed three-SU3 equal-weight fractional c2 cancellation, source-lattice conditional")
print("OPEN correlated U1 quotient classes, spin CS eta, actual normalized full WZ characteristic-class integrality")
