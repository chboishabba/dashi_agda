#!/usr/bin/env python3
"""Negative-control theorem: old adjacent-edge JFine chart is not full D4-stable.

Every E element fixes M=(coarse,N-C,E-C), but conjugating some E translations
by most site-D4 elements moves M. This does not disprove the new opposite-edge
D4-equivariant chart or abstract Monster E-module equivalence.
"""
from json import dumps
from jfine_3b_permutation_heisenberg_action import chart, unchart, act, O
Q=(6,3,0,7,4,1,8,5,2);M=(2,1,0,5,4,3,8,7,6)
ID=tuple(range(9));FIBRE=(7,3,0,2,6,8);LABEL={1,5}
def compose(p,q):return tuple(p[i] for i in q)
def power(p,k):
    ret=ID
    for _ in range(k):ret=compose(ret,p)
    return ret
def perm(p,s):return tuple(s[i] for i in p)
def inv(p):return tuple(p.index(i) for i in range(9))
def A(i):return tuple(int(i==j) for j in range(6)),O,0
def conj(p,g,state):
    k,s=unchart(*state)
    pre=chart(k,perm(inv(p),s))
    k,s=unchart(*act(g,pre))
    return chart(k,perm(p,s))
def audit():
    normalizing=[];obstructed=[]
    for k in range(4):
        r=power(Q,k)
        for name,p in ((f"Q^{k}",r),(f"M Q^{k}",compose(r,M))):
            if {p.index(i) for i in LABEL} == LABEL:
                normalizing.append(name)
                continue
            old=next(i for i in FIBRE if p.index(i) in LABEL)
            source=chart(0,(0,)*9)
            target=conj(p,A(FIBRE.index(old)),source)
            assert source[0] != target[0]
            obstructed.append(dict(d4_element=name,source_fibre_site=old,
                                   target_multiplicity_site=p.index(old)))
    assert len(normalizing)==2 and len(obstructed)==6
    return dict(normalizing_elements=normalizing,non_normalizing_witnesses=obstructed,
                normalizer_in_D4_order=2,total_D4_order=8,
                old_adjacent_edge_chart_fails_full_D4=True,
                scope="chosen E action only; not abstract Monster equivalence")
if __name__=="__main__":print(dumps(audit(),indent=2))
