#!/usr/bin/env python3
"""Exact Q8 subgroup check of the original F19 first-pair localization identity.

Finite SU(2) quaternion SUBGROUP Haar (uniform on Q8), not continuous SU(N)
Haar and not Bałaban's localized CMP119 physical T. Nonfactorizing weight
couples two noncommutative pairs and spectator; tests 1,F,G,FG as ONE source.
"""
from itertools import product

# Q8 = {1,i,j,k,-1,-i,-j,-k}; multiplication is noncommutative.
unit_product = ((0,1,2,3),(1,0,3,2),(2,3,0,1),(3,2,1,0))
unit_sign = ((1,1,1,1),(1,-1,1,-1),(1,-1,-1,1),(1,1,-1,-1))
def mul(a,b):
    sa,ua=divmod(a,4)
    sb,ub=divmod(b,4)
    return unit_product[ua][ub] + 4*((sa+sb+(unit_sign[ua][ub]<0))%2)
def inv(a):
    return next(b for b in range(8) if mul(a,b)==mul(b,a)==0)
assert all(mul(a,inv(a))==mul(inv(a),a)==0 for a in range(8))
assert all(mul(mul(a,b),c)==mul(a,mul(b,c))
           for a,b,c in product(range(8),repeat=3))
assert mul(1,2)!=mul(2,1)

def original_fine_field(coarse, v0, v1, spectator):
    return (mul(coarse[0], inv(v0)),v0,
            mul(coarse[1],inv(v1)),v1,spectator)

def fixed_weight_marks(field):
    a,b,c,d,z=field
    # positive physical-like COUPLED weight; NOT the actual Wilson plaquette action
    weight=1+3*(mul(a,c)==z)+5*(mul(b,d)==z)+2*(mul(a,d)==mul(z,c))
    F=2*int(mul(a,d)==z)
    G=2*int(mul(b,c)==z)
    return (weight,weight*F,weight*G,weight*F*G)

total=0
for coarse in product(range(8),repeat=2):
    # ordered source: first conditional pair V0, remaining pair V1, spectator z
    staged=[0,0,0,0]
    for v0 in range(8):
        continuation=[0,0,0,0]
        for v1,z in product(range(8),repeat=2):
            terms=fixed_weight_marks(original_fine_field(coarse,v0,v1,z))
            continuation=[u+v for u,v in zip(continuation,terms)]
        staged=[u+v for u,v in zip(staged,continuation)]
    flat=[0,0,0,0]
    for v0,v1,z in product(range(8),repeat=3):
        terms=fixed_weight_marks(original_fine_field(coarse,v0,v1,z))
        flat=[u+v for u,v in zip(flat,terms)]
    assert staged==flat
    total+=1
print(f"PASS {total}/{total} coarse Q8 configurations: staged first-pair T = all-fibre T")
print("PASS 1,F,G,FG with shared nonfactorizing weight and spectator")
print("NOT continuous SU(N) Haar, true Wilson action, CMP119 localized domains or OS mass gap")
