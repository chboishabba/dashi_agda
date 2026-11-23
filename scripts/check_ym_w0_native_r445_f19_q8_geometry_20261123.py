#!/usr/bin/env python3
"""Exact finite-group source geometry check of R445 native/F19 pair weld.

Geometry: 4D periodic side-4 positive links; native side-2 coarse bonds;
64 directed coarse bonds = 128 distinct parity-selected fine bonds and
896 spectator fine bonds. Each coarse bond is the ordered two-link path.
Use Q8 subgroup of SU(2) for exact, noncommutative group and site-gauge checks.
Does NOT establish full continuous SU(N) Haar, Bałaban CMP119 localized T,
physical E/R/B/R operations, or continuum mass gap.
"""
from itertools import product

# Real quaternion units 1,i,j,k and their negatives. 0..3 positive, 4..7 negative.
unit_product = ((0,1,2,3), (1,0,3,2), (2,3,0,1), (3,2,1,0))
unit_sign = ((1,1,1,1), (1,-1,1,-1), (1,-1,-1,1), (1,1,-1,-1))
def mul(a,b):
    sa, ua = divmod(a,4)
    sb, ub = divmod(b,4)
    return unit_product[ua][ub] + 4*((sa+sb+(unit_sign[ua][ub]<0))%2)
def inv(a):
    solutions = [b for b in range(8) if mul(a,b)==0 and mul(b,a)==0]
    assert len(solutions)==1
    return solutions[0]
def shift(site, axis, n, modulus=4):
    new=list(site)
    new[axis]=(new[axis]+n)%modulus
    return tuple(new)
def double_site(coarse):
    return tuple(2*v for v in coarse)
def pair_bonds(coarse, axis):
    base=double_site(coarse)
    return (base,axis),(shift(base,axis,1),axis)

sites=list(product(range(4),repeat=4))
coarse_sites=list(product(range(2),repeat=4))
fine_bonds=[(site,axis) for site in sites for axis in range(4)]
coarse_bonds=[(site,axis) for site in coarse_sites for axis in range(4)]
selected=[bond for coarse,axis in coarse_bonds for bond in pair_bonds(coarse,axis)]
assert len(sites)==256 and len(fine_bonds)==1024
assert len(coarse_bonds)==64 and len(selected)==128
assert len(set(selected))==128
spectators=set(fine_bonds)-set(selected)
assert len(spectators)==896
assert set(selected).isdisjoint(spectators)
assert all(shift(first[0],a,1)==second[0] and first[1]==second[1]==a
           for coarse,a in coarse_bonds for first,second in [pair_bonds(coarse,a)])

fine={bond:(5*sum((i+1)*x for i,x in enumerate(bond[0]))+3*bond[1]+1)%8
      for bond in fine_bonds}
gauge={site:(sum((i+2)*x for i,x in enumerate(site))+2)%8 for site in sites}
def transform(bond):
    site,axis=bond
    return mul(mul(gauge[site],fine[bond]),inv(gauge[shift(site,axis,1)]))
assert all(mul(mul(a,b),c)==mul(a,mul(b,c)) for a,b,c in product(range(8),repeat=3))
assert mul(1,2)!=mul(2,1)
for coarse,axis in coarse_bonds:
    first,second=pair_bonds(coarse,axis)
    u,v=fine[first],fine[second]
    native=mul(u,v)
    assert mul(native,inv(v))==u
    assert mul(mul(native,inv(v)),v)==native
    up,vp=transform(first),transform(second)
    native_prime=mul(up,vp)
    assert mul(native_prime,inv(vp))==up
    base=double_site(coarse)
    final=shift(base,axis,2)
    assert native_prime==mul(mul(gauge[base],native),inv(gauge[final]))

# A geometrically explicit off-axis *transported contour* with exactly the
# same coarse endpoints. This is a negative-control path, NOT CMP98 Eq.(15).
# It shows why the published contour-averaged Q need not equal the native W.
nonzero_defects=0
for coarse,axis in coarse_bonds:
    base=double_site(coarse)
    transverse=(axis+1)%4
    base_t=shift(base,transverse,1)
    endpoint=shift(base,axis,2)
    b0=(base,axis); b1=(shift(base,axis,1),axis)
    U=mul(fine[b0],fine[b1])
    detour=[(base,transverse),(base_t,axis),(shift(base_t,axis,1),axis)]
    # traverse +t,+a,+a,-t; last inverse of positive +t at endpoint
    Q=mul(mul(mul(fine[detour[0]],fine[detour[1]]),fine[detour[2]]),
          inv(fine[(endpoint,transverse)]))
    D=mul(Q,inv(U))
    assert mul(D,U)==Q
    if D!=0: nonzero_defects+=1
    Up=mul(transform(b0),transform(b1))
    Qp=mul(mul(mul(transform(detour[0]),transform(detour[1])),transform(detour[2])),
           inv(transform((endpoint,transverse))))
    Dp=mul(Qp,inv(Up))
    assert Qp==mul(mul(gauge[base],Q),inv(gauge[endpoint]))
    assert Dp==mul(mul(gauge[base],D),inv(gauge[base]))
assert nonzero_defects>0
print(f'PASS: off-axis source-path defect Q W^-1 nonzero on {nonzero_defects}/64 bonds')
print('PASS: Q=D W and gauge-adjoint covariance of D at the start site on 64/64 bonds')

print('PASS: Q8 group associativity, inverses and noncommutativity')
print('PASS: native 4D side-4 bond geometry, 64 native coarse paths, 128 disjoint selected fine links')
print('PASS: 896 spectators partition complement; paths have oriented consecutive endpoints')
print('PASS: 64/64 F19 (W,V) inverse and native block reconstruction')
print('PASS: 64/64 local gauge covariance at correct two-step endpoints')
print('FINITE Q8 geometry check only; no full Wilson/Haar RG or CMP119 source-localized T identification')
