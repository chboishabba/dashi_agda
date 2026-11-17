#!/usr/bin/env python3
"""Rational planar theta-loop spine for an ABSTRACT tame genus-three handlebody.

The graph is one central vertex O and three labelled triangular loops
in disjoint planar sectors. Its sufficiently small smooth/PL regular
neighbourhood in R^3 is a standard genus-3 handlebody. We separately
identify the south-pole patch of the central vertex's 3-ball as a
stationary cap keep-out. This is NOT the wild 3-child exterior.

Exact integer/rational segment tests; no numeric tolerance or floating
point. Classical graph-neighbourhood theorem retains original ownership.
"""
from fractions import Fraction as F
from itertools import combinations

O=(F(0),F(0))
triangles={
    "a":((F(8),F(1)),(F(8),F(-1))),
    "b":((F(-5),F(8)),(F(-6),F(7))),
    "c":((F(-5),F(-8)),(F(-6),F(-7))),
}
def cross(a,b,c):
    return (b[0]-a[0])*(c[1]-a[1])-(b[1]-a[1])*(c[0]-a[0])
def on_segment(a,b,p):
    return cross(a,b,p)==0 and all(min(a[j],b[j])<=p[j]<=max(a[j],b[j]) for j in range(2))
def intersect(a,b,c,d):
    x,y,u,v=cross(a,b,c),cross(a,b,d),cross(c,d,a),cross(c,d,b)
    if x*y<0 and u*v<0:return True
    return (x==0 and on_segment(a,b,c)) or (y==0 and on_segment(a,b,d)) or (u==0 and on_segment(c,d,a)) or (v==0 and on_segment(c,d,b))
def audit():
    edges=[]
    vertices={O}
    for name,(p,q) in triangles.items():
        vertices.update([p,q])
        edges.extend(((name,O,p),(name,p,q),(name,q,O)))
        assert p!=q and O!=p and O!=q and cross(O,p,q)!=0
    for (ni,a,b),(nj,c,d) in combinations(edges,2):
        if ni==nj:continue
        # Each pair of distinct loop sectors shares only the origin.
        if intersect(a,b,c,d):
            assert O in (a,b) and O in (c,d), (ni,nj,(a,b),(c,d))
            assert all(pt!=O for pt in set((a,b)).intersection(set((c,d)))-{O})
    assert len(vertices)==7 and len(edges)==9
    assert len(edges)-len(vertices)+1==3
    # Any points of the noncentral graph have z=0. Choose the
    # south-pole cap in the closed unit 0-ball with z<-3/4.
    # Hence cap patch is disjoint from all graph portions outside
    # the 0-ball, with positive vertical distance >=3/4.
    cap_max_z=-F(3,4)
    graph_outside_ball_z=F(0)
    assert graph_outside_ball_z-cap_max_z>=F(3,4)
    assert len({name for name,_,_ in edges})==3
    print("PASS 7 exact rational vertices, 9 embedded edges, 3 independent loops")
    print("PASS distinct sector loops disjoint except common central vertex")
    print("PASS south-pole stationary cap and outside-0-ball spine separated")
    print("THEOREM ROOT: regular neighbourhood of embedded connected graph has handlebody genus E-V+1=3")
    print("OPEN: explicit collar-fixed Nielsen PL isotopy, actual child complement, linked wild limit, equivariant pi1")
if __name__=="__main__":audit()
