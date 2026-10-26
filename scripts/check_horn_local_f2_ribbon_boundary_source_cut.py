#!/usr/bin/env python3
"""Source-positive FINITE Hatcher local F2 ribbon vs false peripheral models.

ORIGINAL SOURCE ROOTS:
Hatcher, Algebraic Topology, Example 2B.2 pp171-172: local
Z is F2 on two genuine meridians and the incoming annulus
generator maps to NONTRIVIAL [a,b] in F2. This is not a
Hopf-link complement (pi1 Z²).
Classical ribbon-graph rotation system: oriented thickening of
a one-vertex/two-edge bouquet gives either a punctured torus
(1 boundary, commutator) or a pair of pants (3 boundaries),
depending on cyclic dart order; Sage ribbon_graph manual is
a later source/implementation, not original mathematical credit.
Agda #1254 owns its OTHER finite simplicial pants constructions.
Agda original horn #1244 owns C3 source satellite 9e_i, R and
local 1/8 affine prototype. Reuse rather than cloning their
complete topology. Selected original SU3 W belongs to #1247.

This script pays an ACTUAL Euclidean straight-two-tube
PUNCTURED-DISK x INTERVAL F2 local metric model, and an
EXACT COMBINATORIAL ribbon boundary/commutator orientation
positive/negative. It does NOT embed the punctured torus
as the REAL Hatcher linked stage, certify relative source
homeomorphism or full wild-exterior avoidance.
"""
from fractions import Fraction as F

holes=((-1,0),(1,0))
core_radius=F(1,8)
meridian_radius=F(1,4)
ambient_disk_radius=F(3)
s=F(1,8)
assert holes[1][0]-holes[0][0]==2>2*meridian_radius
assert meridian_radius-core_radius==F(1,8)>0
assert 2-meridian_radius-core_radius==F(13,8)>0
assert F(1)+meridian_radius<ambient_disk_radius
length_upper=2*F(22,7)*s*meridian_radius
assert length_upper==F(11,56)<F(781,1000)
assert F(1,4)+s*(F(1)+meridian_radius)==F(13,32)<1
print('PASS actual finite 2-straight-tube local F2 meridian circles, clearance and L<11/56')

# The cylinder-deleted D² x I product deformation retracts
# onto a 2-punctured planar disk, hence pi1=F2. Its local
# free generators are based meridians around each deletion.
# Distinct BASED whiskers are required to represent both
# at a common basepoint. No actual Hatcher cap is assumed.

dart=('a','A','b','B')
flip={'a':'A','A':'a','b':'B','B':'b'}
def rotation(cycle):
    assert set(cycle)==set(dart) and len(cycle)==4
    return {cycle[i]:cycle[(i+1)%4] for i in range(4)}
def cycles_of(perm):
    seen=set();cc=[]
    for h in dart:
        if h in seen:continue
        one=[];x=h
        while x not in seen:
            seen.add(x);one.append(x);x=perm[x]
        assert x==h
        cc.append(tuple(one))
    return cc
def ribbon_at_vertex(cyclic):
    sigma=rotation(cyclic)
    # Boundary traversal crosses edge flip then follows rotation.
    phi={h:sigma[flip[h]] for h in dart}
    boundary=cycles_of(phi)
    V,E=1,2
    chi=V-E
    count=len(boundary)
    twice_genus=2-count-chi
    assert twice_genus>=0 and twice_genus%2==0
    return boundary,count,twice_genus//2,chi

torus,bt,gt,chi=ribbon_at_vertex(('a','B','A','b'))
pants,bp,gp,_=ribbon_at_vertex(('a','A','b','B'))
assert (bt,gt,chi)==(1,1,-1)
assert (bp,gp)==(3,0)
assert torus==[('a','b','A','B')]
assert sorted(len(q) for q in pants)==[1,1,2]
print('PASS alternating ONE-boundary genus1 ribbon word [a,b] source-positive')
print('PASS nonalternating THREE-boundary genus0 pants source-negative on SAME abstract F2')

# Exact reduced group word: Hatcher incoming annulus is nonzero
# in F2 but dies under abelianisation (or any Hopf Z² source).
def free_reduce(w):
    a=[]
    for x in w:
        if a and a[-1]==-x:a.pop()
        else:a.append(x)
    return tuple(a)
boundary_word=free_reduce((1,2,-1,-2))
assert boundary_word==(1,2,-1,-2)!=()
assert sum(1 if x>0 else -1 for x in boundary_word if abs(x)==1)==0
assert sum(1 if x>0 else -1 for x in boundary_word if abs(x)==2)==0
print('PASS Hatcher source: free commutator NONZERO, abelianisation zero')

# Source C3 placement of local standard F2 two meridians is
# geometrically cheap but STILL needs a real Hatcher Z->satellite
# based homeomorphism identifying this exact punctured-torus
# boundary circle, not just a suitable ribbon graph.
R=lambda q:(q[2],q[0],q[1])
cs=((F(9),F(0),F(0)),(F(0),F(9),F(0)),(F(0),F(0),F(9)))
def embed(c,p):
    v=(F(1,4)+s*p[0],s*p[1],F(0))
    for _ in range(c):v=R(v)
    return tuple(cs[c][j]+v[j] for j in range(3))
for c in range(3):
    for p in ((F(-1),F(0)),(F(1),F(0)),
              (F(-5,4),F(0)),(F(5,4),F(0))):
        assert R(embed(c,p))==embed((c+1)%3,p)
print('PASS model F2 2-tube C3 three-satellite length transfer (NOT source wild map)')
print('OPEN relative actual Hatcher punctured-torus embedding, annulus map, meridian marking, whole-stage source clearance')
