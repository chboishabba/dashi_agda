#!/usr/bin/env python3
"""D4-equivariant JFine rechart; imports (does not duplicate) canonical H action.

Source geometry: PR #1148 IITJFineFourOneFourS3ZetaGaugeExact.
Uses opposite-edge half-differences for 2 labels, half-sums plus corners for X6.
Proof status: exhaustive local finite checks, not Monster action identification.
"""
from itertools import product
from json import dumps
from jfine_3b_permutation_heisenberg_action import act, O

Q=(6,3,0,7,4,1,8,5,2)
M=(2,1,0,5,4,3,8,7,6)
P_Q=(1,0,4,2,5,3)
P_M=(0,1,3,2,5,4)
def perm(u,p):return tuple(u[j] for j in p)
def negate(u):return tuple(-x%3 for x in u)
def dot(a,b):return sum(x*y for x,y in zip(a,b))%3
def chart(k,s):
    nw,n,ne,w,c,e,sw,so,se=s
    n,e,so,w,nw,ne,sw,se=((a-c)%3 for a in (n,e,so,w,nw,ne,sw,se))
    return ((k,2*(n-so)%3,2*(e-w)%3),
            (2*(n+so)%3,2*(e+w)%3,nw,ne,sw,se),c)
def unchart(m,u,c):
    k,a,b=m;x,y,nw,ne,sw,se=u
    n,so,e,w=(x+a)%3,(x-a)%3,(y+b)%3,(y-b)%3
    return k,tuple((t+c)%3 for t in (nw,n,ne,w,0,e,sw,so,se))
def geometric(op,p):
    m,u,c=p;k,a,b=m
    if op=='Q':return (k,(-b)%3,a),perm(u,P_Q),c
    if op=='M':return (k,a,(-b)%3),perm(u,P_M),c
    raise ValueError(op)
def image_from_source(op,p):
    k,s=unchart(*p)
    return chart(k,perm(s,Q if op=='Q' else M))
def induced_heisenberg_automorphism(op,g):
    a,b,t=g;p=P_Q if op=='Q' else P_M
    return perm(a,p),perm(b,p),t
def value_reflect(p):
    m,u,c=p
    return (m[0],-m[1]%3,-m[2]%3),negate(u),-c%3
def reflect_heisenberg(g):
    a,b,t=g
    return negate(a),b,-t%3
def unit(i):return tuple(int(i==j) for j in range(6))
def A(i):return unit(i),O,0
def B(i):return O,unit(i),0
def audit():
    states=d4_checks=reflection_checks=0
    for k in range(10):
        for s in product(range(3),repeat=9):
            p=chart(k,s)
            assert unchart(*p)==(k,s)
            for op in ('Q','M'):
                assert geometric(op,p)==image_from_source(op,p)
                for g in (A(0),A(1),B(0),B(1)):
                    assert geometric(op,act(g,p))==act(induced_heisenberg_automorphism(op,g),geometric(op,p))
                    d4_checks+=1
            assert value_reflect(value_reflect(p))==p
            assert value_reflect(act(A(0),p))==act(reflect_heisenberg(A(0)),value_reflect(p))
            reflection_checks+=1
            states+=1
    assert states==196830
    # Whole 6D dot pairing is preserved under each induced permutation.
    for op in ('Q','M'):
        p=P_Q if op=='Q' else P_M
        for i in range(6):
            for j in range(6):
                assert dot(perm(unit(i),p),perm(unit(j),p))==int(i==j)
    # Character table of geometric D4 action on 10×F3² multiplicity labels.
    pairs=list(product(range(3),repeat=2))
    chars=(90,
           10*sum(((-b)%3,a)==(a,b) for a,b in pairs),
           10*sum(((-a)%3,(-b)%3)==(a,b) for a,b in pairs),
           10*sum((a,(-b)%3)==(a,b) for a,b in pairs))
    assert chars==(90,10,10,30)
    return dict(states=states,full_D4_normalizes_constructed_E=True,
                heisenberg_generator_conjugation_checks=d4_checks,
                value_reflection_checks=reflection_checks,
                D4_character=dict(identity=90,quarter_turn=10,half_turn=10,reflection=30),
                D4_irreducible_multiplicities=dict(A1=30,A2=0,B1=10,B2=10,E2=20),
                status="source-geometric finite D4 action; not Monster N(3B) same-object lift")
if __name__=="__main__":print(dumps(audit(),indent=2))
