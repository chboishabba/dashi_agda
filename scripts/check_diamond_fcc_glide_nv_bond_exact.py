#!/usr/bin/env python3
"""Exact source-bounded diamond fcc / glide / NV bond stabilizer audit.

Classical crystallographic sources: IUCr ITC Vol A Fd-3m (227),
AFLOW A_cF8_227_a-001. Coordinates are quarter conventional-cell units.
The site set is FCC ∪ ((1,1,1)+FCC), not the 27-point ternary cube.
No Hamiltonian, device calibration, quantum advantage, or measured material
property is inferred. PR #1249 retains ownership of PG(2,3) cube axes.
"""
from itertools import product, permutations

D=(1,1,1)
O=(0,0,0)
def add(x,y): return tuple(a+b for a,b in zip(x,y))
def sub(x,y): return tuple(a-b for a,b in zip(x,y))
def fcc(t):
    u,v,w=t
    return (2*(v+w),2*(u+w),2*(u+v))
def fromfcc(v):
    x,y,z=v
    ns=(y+z-x,x+z-y,x+y-z)
    return tuple(n//4 for n in ns) if all(n%4==0 for n in ns) else None
def flipx_primitive(t):
    u,v,w=t
    return (u+v+w,-w,-v)
def swap_xy(t):
    u,v,w=t
    return (v,u,w)
def swap_yz(t):
    u,v,w=t
    return (u,w,v)
def at(s):
    label,t=s
    return add(fcc(t),D if label=='B' else O)
def glide(s):
    label,t=s
    f=flipx_primitive(t)
    return ('B',f) if label=='A' else ('A',add(f,(1,0,0)))
def glide_geometry(x):
    return add(D,(-x[0],x[1],x[2]))
def site_swap(s,m):
    return s[0],m(s[1])

for t in product(range(-3,4),repeat=3):
    assert fromfcc(fcc(t))==t
    assert fcc(flipx_primitive(t))==(-fcc(t)[0],fcc(t)[1],fcc(t)[2])
    assert fcc(swap_xy(t))==(fcc(t)[1],fcc(t)[0],fcc(t)[2])
    assert fcc(swap_yz(t))==(fcc(t)[0],fcc(t)[2],fcc(t)[1])
    for label in ('A','B'):
        s=(label,t)
        assert at(glide(s))==glide_geometry(at(s))
        assert glide(glide(s))==(label,add(t,(1,0,0)))
        assert at(site_swap(s,swap_xy))==(at(s)[1],at(s)[0],at(s)[2])
        assert at(site_swap(s,swap_yz))==(at(s)[0],at(s)[2],at(s)[1])

G=[(p,s) for p in permutations(range(3))
         for s in product((-1,1),repeat=3)]
assert len(G)==48
def linear(g,x):
    p,s=g
    return tuple(s[i]*x[p[i]] for i in range(3))
def glide_coset(g):
    return D if sum(s<0 for s in g[1])%2 else O
def operate(g,x): return add(linear(g,x),glide_coset(g))
def multiply(g,h):
    p,s=g; q,t=h
    return tuple(q[p[i]] for i in range(3)),tuple(s[i]*t[p[i]] for i in range(3))

# Affine representatives are closed modulo actual FCC translations:
# c(g,h)=t(g)+g*t(h)-t(gh) ∈ FCC.
for g,h in product(G,repeat=2):
    cocycle=sub(add(glide_coset(g),linear(g,glide_coset(h))),
                glide_coset(multiply(g,h)))
    assert fromfcc(cocycle) is not None,(g,h,cocycle)

# Each of 48 representative operations maps every tested A/B site
# into exactly one occupied FCC coset, with an exact primitive inverse.
for g in G:
    for label in ('A','B'):
        for t in product(range(-1,2),repeat=3):
            target=operate(g,at((label,t)))
            a=fromfcc(target)
            b=fromfcc(sub(target,D))
            assert (a is None) != (b is None),(g,label,t)
            assert at(('A',a) if a is not None else ('B',b))==target

# Site-symmetry vs bond-symmetry are distinct: A(0) is fixed by
# 24 operations; ordered bond (A(0),B(delta)) is fixed by 6.
origin_fix=[g for g in G if operate(g,O)==O]
bond_fix=[g for g in origin_fix if operate(g,D)==D]
assert len(origin_fix)==24 and len(bond_fix)==6
assert all(g[1]==(1,1,1) for g in bond_fix)
assert {g[0] for g in bond_fix}==set(permutations(range(3)))

print("PASS FCC primitive lattice, diamond A/B motif, exact inverse & glide squared")
print("PASS 48 cubic operation representatives close modulo FCC translations")
print("PASS atomic-site stabilizer 24; ordered [111] bond stabilizer 6 = S3/C3v")

# Conventional cubic cell: four FCC centring translations modulo 4.
# 48 inequivalent linear parts x 4 centring translations = 192
# affine operations, and 8 diamond sites per conventional cell.
centring={(0,0,0),(0,2,2),(2,0,2),(2,2,0)}
def mod4(x): return tuple(n%4 for n in x)
operators={(g,mod4(add(glide_coset(g),t)))
           for g in G for t in centring}
assert len(operators)==192
motif={mod4(add(fcc(t),delta))
       for t in product((0,1),repeat=3)
       for delta in (O,D)}
assert len(motif)==8
for g,t in operators:
    assert {mod4(add(linear(g,p),t)) for p in motif}==motif
for (g,t),(h,u) in product(operators,repeat=2):
    gh=multiply(g,h)
    v=mod4(add(t,linear(g,u)))
    assert (gh,v) in operators

site_stab=sum(mod4(add(linear(g,O),t))==O
              for g,t in operators)
bond_stab=sum(
    mod4(add(linear(g,O),t))==O and
    mod4(add(linear(g,D),t))==D
    for g,t in operators)
assert site_stab==24 and bond_stab==6
print("PASS: 192 conventional-cell affine operations and all 36864 products")
print("PASS: 8 diamond motif sites, site stabilizer 24, oriented bond C3v 6")

# Three independently published IUCr Fd-3m origin-choice-1 operations:
# (2)  (-x,-y+1/2,z+1/2)
# (13) (y+3/4,x+1/4,-z+3/4)
# (25) (-x+1/4,-y+1/4,-z+1/4)
assert (((0,1,2),(-1,-1,1)),(0,2,2)) in operators
assert (((1,0,2),(1,1,-1)),(3,1,3)) in operators
assert (((0,1,2),(-1,-1,-1)),(1,1,1)) in operators
print("PASS: three literal IUCr Fd-3m origin-choice-1 operations")

# Reciprocal FCC vectors are conventional cubic integer wavevectors
# (kx,ky,kz) whose components have equal parity (a bcc index lattice).
# The genuine reciprocal test is pairing divisible by four in the
# quarter-cell coordinate convention; checks include both directions.
primitive_generators=[fcc((1,0,0)),fcc((0,1,0)),fcc((0,0,1))]
def dot(p,k):return sum(a*b for a,b in zip(p,k))
for k in product(range(-3,4),repeat=3):
    valid=all(dot(t,k)%4==0 for t in primitive_generators)
    same_parity=(k[0]-k[1])%2==0 and (k[1]-k[2])%2==0
    assert valid==same_parity
for u,v,w,a,b,c,s in product((-1,0,1),repeat=7):
    t=fcc((u,v,w))
    k=(2*a+s,2*b+s,2*c+s)
    n=a*(v+w)+b*(u+w)+c*(u+v)+s*(u+v+w)
    assert dot(t,k)==4*n
print("PASS: FCC↔BCC reciprocal criterion on 343 wavevectors;")
print("PASS: universal quartic-index pairing identity on 2187 integer fixtures")
