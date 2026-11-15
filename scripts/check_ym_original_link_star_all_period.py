#!/usr/bin/env python3
"""Original positive Wilson bond conflict 6/18/19 period regression.

Mathematical proof: a link (x,mu) belongs to only the two
(mu,nu)-plaquettes based at x and x-e_nu for each nu != mu.
Each of the <=6 plaquettes contains <=3 other positive bond
variables, so <=18 other links and <=19 closed neighbours.
This script checks candidate-set completeness, including L=1,2,
against exhaustive original Wilson positive-bond supports.

This executable check is NOT an Agda kernel proof for arbitrary n.
"""
from itertools import product, combinations

def verify(L):
    sites=list(product(range(L),repeat=4))
    def shift(x,axis,sign=1):
        y=list(x)
        y[axis]=(y[axis]+sign)%L
        return tuple(y)
    def support(x,mu,nu):
        return frozenset(((x,mu),(shift(x,mu),nu),
                          (shift(x,nu),mu),(x,nu)))
    plaquettes={(x,mu,nu):support(x,mu,nu)
                for x in sites for mu,nu in combinations(range(4),2)}
    incident={(x,mu):set() for x in sites for mu in range(4)}
    for p,bs in plaquettes.items():
        for b in bs:
            incident[b].add(p)
    max_other=0
    for (x,mu),actual in incident.items():
        b=(x,mu)
        canonical=set()
        for nu in range(4):
            if nu==mu:continue
            mn=tuple(sorted((mu,nu)))
            canonical.add((x,*mn))
            canonical.add((shift(x,nu,-1),*mn))
        assert actual==canonical, (L,b,'six-plane coverage')
        neighbours=set()
        for p in actual:
            assert b in plaquettes[p]
            neighbours.update(plaquettes[p])
        others=neighbours-{b}
        assert len(actual)<=6 and len(others)<=18
        assert len(neighbours)<=19
        max_other=max(max_other,len(others))
    return L,len(incident),len(plaquettes),max_other

if __name__=="__main__":
    for L in (1,2,3,4,5):
        print('L, bonds, plaquettes, max-other:',*verify(L))
