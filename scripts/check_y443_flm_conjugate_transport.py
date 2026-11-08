#!/usr/bin/env python3
"""Exact nonidentity same-VOA-action transport regression (finite CONTROL).

Uses a rational 5-atom algebra under a genuine unimodular change of basis,
the full 120-element automorphism group, two generators, and a deliberately
distinct second action. Not an FLM VOA, Monster matrix, or Y443 isomorphism.
"""
from collections import deque
from fractions import Fraction as F
from itertools import product
import json

I=tuple(range(5));Z=F(0);O=F(1)
def compose(p,q):return tuple(p[q[i]] for i in I)
def inverse(p):
    r=[0]*5
    for i,j in enumerate(p):r[j]=i
    return tuple(r)
def permute(p,x):
    v=inverse(p)
    return tuple(x[v[i]] for i in I)
def to_canonical(x):
    return tuple(x[i]+(x[i+1] if i<4 else 0) for i in I)
def from_canonical(y):
    x=[Z]*5
    for i in reversed(I):x[i]=y[i]-(x[i+1] if i<4 else 0)
    return tuple(x)
def basis(k):return tuple(O if i==k else Z for i in I)
def add(x,y):return tuple(a+b for a,b in zip(x,y))
def canonical_product(x,y):return tuple(a*b for a,b in zip(x,y))
def selected_product(x,y):return from_canonical(canonical_product(to_canonical(x),to_canonical(y)))
def selected_action(p,x):return from_canonical(permute(p,to_canonical(x)))
def main():
    u=(1,2,3,4,0);v=(1,0,2,3,4);identity=I
    words={identity:()};queue=deque([identity])
    while queue:
        g=queue.popleft()
        for symbol,h in (('u',u),('v',v)):
            k=compose(g,h)
            if k not in words:words[k]=words[g]+(symbol,);queue.append(k)
    assert len(words)==120
    checked=0
    for g in words:
        for i in I:
            x=basis(i)
            assert from_canonical(to_canonical(x))==x
            assert to_canonical(from_canonical(x))==x
            assert to_canonical(selected_action(g,x))==permute(g,to_canonical(x))
            checked+=3
        for i,j in product(I,repeat=2):
            x,y=basis(i),basis(j)
            assert to_canonical(selected_product(x,y))==canonical_product(to_canonical(x),to_canonical(y))
            assert selected_action(g,selected_product(x,y))==selected_product(selected_action(g,x),selected_action(g,y))
            assert selected_action(g,add(x,y))==add(selected_action(g,x),selected_action(g,y))
            checked+=3
        unit=from_canonical((O,)*5)
        assert selected_action(g,unit)==unit;checked+=1
        for i in I:
            x=basis(i)
            for letter in reversed(words[g]):
                x=selected_action(u if letter=='u' else v,x)
            assert x==selected_action(g,basis(i));checked+=1
    for g,h in product(words,repeat=2):
        for i in I:
            x=basis(i)
            assert selected_action(compose(g,h),x)==selected_action(g,selected_action(h,x))
            checked+=1
    c=(1,2,0,3,4)
    def different(g,x):return selected_action(compose(compose(c,g),inverse(c)),x)
    assert any(different(u,basis(i))!=selected_action(u,basis(i)) for i in I)
    assert any(different(v,basis(i))!=selected_action(v,basis(i)) for i in I)
    print(json.dumps({
        'status':'PASS','scope':'Q^5 finite algebra, NOT actual Vnatural',
        'nontrivial_exact_linear_isomorphism':True,
        'actual_preserved_selected_product':True,
        'group_coverage':len(words),
        'two_generator_action_composition':True,
        'exact_checks':checked,
        'wrong_second_action_detected_on_both_generators':True,
        'actual_selected_FLM_VOA_isomorphism_present':False,
        'actual_Y443_Monster_source_isomorphism_present':False
    },indent=2))
if __name__=='__main__':main()
