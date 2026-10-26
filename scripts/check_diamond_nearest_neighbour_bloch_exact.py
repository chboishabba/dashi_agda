#!/usr/bin/env python3
"""Exact 4-bond ideal-diamond 2-band Bloch and cubic-symmetry audit.

Geometry: DASHI/Mathematics/Symmetry/DiamondFccPrimitiveGlideExact.agda.
Fourth-root arithmetic: DiamondEightSiteStructureFactorExact.agda.
Original physical prior art: Fu–Kane–Mele diamond nearest-neighbour
model (Physical Review B 76, 045302, 2007); see the precise model
assumptions documented in diamond_nn_bloch_symmetry_20261026.md.

This does not infer actual diamond electronic/optical bandgaps, an NV
spin spectrum, a physical quantum computer or a calibrated device.
"""
from itertools import permutations,product
from collections import Counter

ROOT=((1,0),(0,1),(-1,0),(0,-1))
D=((1,1,1),(1,-1,-1),(-1,1,-1),(-1,-1,1))
def add(a,b):return (a[0]+b[0],a[1]+b[1])
def mul(a,b):return (a[0]*b[0]-a[1]*b[1],a[0]*b[1]+a[1]*b[0])
def conj(a):return (a[0],-a[1])
def norm(a):return a[0]*a[0]+a[1]*a[1]
def gamma(k):
    out=(0,0)
    for d in D:
        out=add(out,ROOT[sum(x*y for x,y in zip(k,d))%4])
    return out
def bloch2(k):
    v=gamma(k)
    return (((0,0),v),(conj(v),(0,0)))
def swap_basis(H):
    return ((H[1][1],H[1][0]),(H[0][1],H[0][0]))
def b3_action(p,s,k):
    return tuple((s[i]*k[p[i]])%4 for i in range(3))
def fcc(u,v,w):
    return (2*(v+w),2*(u+w),2*(u+v))
def add3(a,b):return tuple(x+y for x,y in zip(a,b))

# Recover exact nearest-neighbour coordinates from the existing
# FCC primitive model: B(0),B(-e1),B(-e2),B(-e3).
offset=(1,1,1)
neighbours=tuple(add3(fcc(*q),offset) for q in (
    (0,0,0),(-1,0,0),(0,-1,0),(0,0,-1)))
assert neighbours==D
assert all(sum(x*x for x in v)==3 for v in neighbours)
assert len(set(neighbours))==4

values=Counter()
allk=list(product(range(4),repeat=3))
allg=list(product(permutations(range(3)),product((-1,1),repeat=3)))
assert len(allk)==64 and len(allg)==48
for k in allk:
    gk=gamma(k)
    # Hamiltonian H=[[0,gamma],[conj gamma,0]]:
    # both diagonals of H^2 equal |gamma|² exactly in Z[i].
    h2=mul(gk,conj(gk))
    assert h2==(norm(gk),0)
    assert mul(conj(gk),gk)==h2
    assert h2[0] in (0,16)
    values[h2[0]]+=1
    for p,s in allg:
        transformed=gamma(b3_action(p,s,k))
        expected=conj(gk) if s.count(-1)%2 else gk
        assert transformed==expected, (k,p,s,transformed,expected)
        assert norm(transformed)==norm(gk)
        target=swap_basis(bloch2(k)) if s.count(-1)%2 else bloch2(k)
        assert bloch2(b3_action(p,s,k))==target
assert values==Counter({0:48,16:16}),values

assert gamma((0,0,0))==(4,0)
assert gamma((1,0,0))==(0,0)
assert gamma((1,1,1))==(0,-4)

# Translation/basis gauge caveat: this Bloch bond amplitude sums
# FOUR local hopping vectors, not all EIGHT conventional-cell
# occupied sites. Diffraction and tight-binding are separate operators.
fcc4=((0,0,0),(0,2,2),(2,0,2),(2,2,0))
diamond8=fcc4+tuple(add3(x,offset) for x in fcc4)
def diffraction(k):
    out=(0,0)
    for x in diamond8:
        out=add(out,ROOT[sum(a*b for a,b in zip(k,x))%4])
    return out
assert diffraction((1,0,0))==(0,0)
assert diffraction((0,0,0))==(8,0)
assert gamma((0,0,0))==(4,0)
print("PASS: four real A→B FCC neighbours recovered without invented bonds")
print("PASS: all 3072 sampled B3 maps; odd sign parity conjugates Gamma")
print("PASS: matrix-level H(gk)=sigma_x H(k) sigma_x for odd sign parity")
print("PASS: exact Hermitian H²=norm² I on all 64 momentum residues")
print("PASS: sampled |Gamma|² distribution: 0=48; 16=16")
print("PASS: tight-binding vs diffraction phases/operators kept distinct")
