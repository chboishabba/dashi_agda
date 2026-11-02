#!/usr/bin/env python3
"""Full 27 local pure SU3^3 parity/CS mass-sign chambers (NOT global CS).

Representations from classical E6 trinification:
(3,bar3,1) + (bar3,1,3) + (1,3,bar3). Chosen local
five-dimensional parity-odd Dirac convention:
k_G^induced = 1/2 sum sign(M_block) A_G(block)*multiplicity.
Mass signs may change across actual background Higgs/spurion walls.
It is NOT a proof of mixed SU3^2 U1, gravitational terms,
regulator/APS eta or spin/(SU3^3 x U1)/discrete quotient.
Prior physics: Bonetti/Grimm/Hohenegger JHEP07(2013)043.
"""
from fractions import Fraction
from itertools import product
def half_level(signs):
    A,B,C=signs
    return (Fraction(3*(A-B),2),Fraction(3*(C-A),2),
            Fraction(3*(B-C),2))
all_chambers={s:half_level(s) for s in product((-1,1),repeat=3)}
assert len(all_chambers)==8
for signs,k in all_chambers.items():
    assert sum(k)==0
    assert all(x.denominator==1 and abs(x)<=3 for x in k)
    print("mass signs",signs,"pure SU3c,L,R conditional half-levels",k)
assert half_level((1,1,1))==half_level((-1,-1,-1))==(0,0,0)
assert half_level((1,-1,1))==(3,0,-3)
print("PASS uniform mass sign zero local pure SU3 cubic index for full27")
print("PASS component-dependent signs change INDUCED CS even though sum cubic index zero")
print("OPEN bare CS levels, regulator, global quotient, chiral/brane spectrum, real full-E6 action")
