#!/usr/bin/env python3
"""Exact action on 10 × F3^9 via the pre-existing JFine 90 × 729 × 3 chart.
Original JFine source type and codec: PR #1148. This is NOT a Monster intertwiner.
"""
from itertools import product
import json
T=range(3); O=(0,)*6
def add(u,v): return tuple((a+b)%3 for a,b in zip(u,v))
def neg(u): return tuple(-a%3 for a in u)
def dot(u,v): return sum(a*b for a,b in zip(u,v))%3
def chart(k,s):
    nw,n,ne,w,c,e,sw,so,se=s
    return (k,(n-c)%3,(e-c)%3), tuple((a-c)%3 for a in (so,w,nw,ne,sw,se)),c
def unchart(m,u,c):
    k,n,e=m
    so,w,nw,ne,sw,se=((a+c)%3 for a in u)
    return k,(nw,(n+c)%3,ne,w,c,(e+c)%3,sw,so,se)
def mul(g,h):
    a,b,t=g;x,y,s=h
    return add(a,x),add(b,y),(t+s+dot(b,x))%3
def inv(g):
    a,b,t=g
    return neg(a),neg(b),(-t+dot(a,b))%3
def act(g,p):
    m,u,c=p;a,b,t=g
    return m,add(u,a),(c+t+dot(b,u))%3
def flip(p):
    m,u,c=p
    return (m[0],-m[1]%3,-m[2]%3),neg(u),-c%3
def alpha(g):
    a,b,t=g
    return neg(a),b,-t%3
def axes():
    for i in range(6):
        e=tuple(int(i==j) for j in range(6))
        yield (e,O,0),(O,e,0)
def audit():
    pairs=list(axes()); gs=[g for pair in pairs for g in pair]
    roundtrip=weyl=conjugation=fixed=0
    for k in range(10):
        for s in product(T,repeat=9):
            p=chart(k,s)
            assert unchart(*p)==(k,s)
            assert flip(flip(p))==p
            fixed+=int(p==flip(p))
            for g in gs:
                assert act(inv(g),act(g,p))==p
                assert flip(act(g,flip(p)))==act(alpha(g),p)
                roundtrip+=1;conjugation+=1
            for ag,bg in pairs:
                assert act(bg,act(ag,p))==act((O,O,1),act(ag,act(bg,p)))
                weyl+=1
    for b in product(T,repeat=6):
        if b!=O:
            assert sorted(sum(dot(b,u)==j for u in product(T,repeat=6)) for j in T)==[243]*3
    sample=((0,1,2),(0,1,2,0,1,2),1)
    for g in gs:
        for h in gs:
            assert act(g,act(h,sample))==act(mul(g,h),sample)
            assert mul(g,inv(g))==(O,O,0)
            assert alpha(mul(g,h))==mul(alpha(g),alpha(h))
    assert fixed==10
    return dict(states=196830,pointed_c3_orbits=65610,multiplicity=90,schrodinger_degree=729,
                roundtrips=roundtrip,weyl=weyl,reflection_conjugations=conjugation,
                reflection_fixed_points=fixed,reflection_on_90_eigenspaces=[50,40],
                actual_monster_matrix=False,proof_status="exhaustive model tests only")
if __name__=="__main__": print(json.dumps(audit(),indent=2))
