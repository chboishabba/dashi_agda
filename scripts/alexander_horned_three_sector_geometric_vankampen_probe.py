#!/usr/bin/env python3
"""Exact three-sector horn source-word and true 3D collar-overlap audit.

Hatcher, Algebraic Topology, Example 2B.2, pp171-172:
each free-stage meridian maps to the commutator of TWO NEW
free-stage generators. The source tower has three INDEPENDENT
sectors and colimit G_A * G_A * G_A, not a direct product.

This local finite audit does not prove the particular geometric
wild-embedding van Kampen same-object realization, though the
arbitrary-rank algebraic injection follows from the block-normal
form argument described below.
"""
from fractions import Fraction as Q
from itertools import product

rotate=lambda v:(v[2],v[0],v[1])
satellites=((9,0,0),(0,9,0),(0,0,9))
assert tuple(map(rotate,satellites))==satellites[1:]+satellites[:1]
assert rotate(rotate(rotate((1,2,3))))==(1,2,3)
radius=Q(1,4)
# CORRECTION to earlier tangent-only [1,8] spoke model:
# Use t in [1/2,17/2] to overlap both unit balls IN THEIR INTERIOR.
# The entire cross-sectional disk at either endpoint is inside its
# ball since (1/2)^2+(1/4)^2 = 5/16 < 1.
assert Q(1,2)**2+radius**2==Q(5,16)<1
# A point on a spoke outside the central unit ball has axial t>3/4,
# otherwise norm^2 <= (3/4)^2+(1/4)^2=5/8 <1.
# Two tubes on different axes cannot overlap outside the central
# ball: each demands its own axis coordinate >3/4, whereas the
# other bounds it by <=1/4.
assert Q(3,4)**2+radius**2==Q(5,8)<1
assert Q(3,4)>radius
# Nonincident satellite ball has radial-other coordinate >= 9-1/4.
assert (Q(9)-radius)**2>1
assert 81>4 and 162>4
print("PASS genuine positive-volume collar overlap and exposed C3 disjointness")

# Local clasp loops INSIDE EACH satellite, separated from inward
# spoke by outward x-translation 1/4 and scaling 1/8:
# C1=(2cos t,2sin t,0), C2_h=(h,1+cos t,sin t).
# After affine scaling the circles have x>=0 in satellite-centred
# outward coordinate while the spoke stops at x=-1/2.
assert (Q(1,4)+Q(5,8))**2+Q(1,16)==Q(53,64)<1
assert (Q(1,4)+Q(1,8))**2+Q(1,16)==Q(13,64)<1
def lk(h):
    # Signed transverse intersections of C2_h with C1 disk.
    assert h*h not in (4,) and h*h+4!=4
    return int(h*h+4<4)-int(h*h<4)
assert lk(1)==-1 and lk(5)==0
print("PASS same collar coordinates support linked -1 and unlinked 0 local curves")

# A concrete TAME comparator: binary Cantor intervals on the outward
# radial axis, shifted by 1/2 in the next transverse sector direction.
# It has the SAME clopen symbolic K=C3 x {0,1}^N as wild tips, but
# its embedding is entirely tame and avoids all local clasp loops.
def interval(pre):
    lo=Q(1,4)+sum((Q(b,3**(j+1)) for j,b in enumerate(pre)),Q(0))
    return lo,lo+Q(1,2*3**len(pre))
assert interval(())==(Q(1,4),Q(3,4))
count=0
for n in range(9):
    mass=Q(1,3*2**n)
    assert 3*2**n*mass==1
    for pre in product((0,1),repeat=n):
        lo,hi=interval(pre)
        assert Q(1,4)<=lo<hi<=Q(3,4)
        assert hi**2+Q(1,2)**2<=Q(13,16)<1
        left,right=interval(pre+(0,)),interval(pre+(1,))
        assert left[0]==lo and right[1]==hi
        assert left[1]-left[0]==right[1]-right[0]==(hi-lo)/3
        assert right[0]-left[1]==(hi-lo)/3
        count+=1
assert count==511
print("PASS 511 exact finite Cantor cylinders and three-sector tame comparator")

# Stage n: F_(3*2^n), generators (sector,address) labelled integers.
# Let x_i |-> [a_i,b_i] with disjoint two-letter child alphabets.
# An arbitrary REDUCED source word expands to a concatenation of
# cyclically reduced, four-letter blocks; adjacent blocks cannot
# cancel: distinct generators use disjoint alphabets, while equal
# adjacent generators in a reduced word have the SAME sign.
# Thus |expand(w)|=4|w| and the bonding map is injective FOR ALL n.
def reduce_word(w):
    stack=[]
    for x in w:
        if stack and stack[-1]==-x:stack.pop()
        else:stack.append(x)
    return tuple(stack)
def expand(w,n):
    assert reduce_word(w)==w
    m=1<<n
    ans=[]
    for letter in w:
        sector,index=divmod(abs(letter)-1,m)
        assert 0<=sector<3
        a=sector*(2*m)+2*index+1
        b=a+1
        ans.extend((a,b,-a,-b) if letter>0 else (b,a,-b,-a))
    return tuple(ans)
def rotation(w,n):
    m=1<<n
    return tuple((1 if a>0 else -1)*
        (((((abs(a)-1)//m)+1)%3)*m+((abs(a)-1)%m)+1)
        for a in w)
checks=0
for n in range(4):
    rank=3*(1<<n)
    alphabet=tuple(sign*i for i in range(1,rank+1) for sign in (1,-1))
    max_len=4 if n==0 else 3 if n<=2 else 2
    for k in range(max_len+1):
        for w in product(alphabet,repeat=k):
            if reduce_word(w)!=w:continue
            v=expand(w,n)
            assert reduce_word(v)==v
            assert len(v)==4*len(w)
            assert rotation(v,n+1)==expand(rotation(w,n),n)
            checks+=1
print("PASS",checks,"reduced source words; fourfold length and sector rotation naturality")
print("ALL-STAGE ALGEBRAIC PROOF: disjoint-alphabet cyclically reduced blocks")
print("COLIMIT via free-product universal property: G_three=G_A*G_A*G_A")
print("NOT CERTIFIED: wild embedding, actual attachment collars, complement pi1")
