#!/usr/bin/env python3
"""Original periodic 4D Wilson plaquette-star conflict and packing assay.

Only SOURCE FINITE GEOMETRY: 6 incident plaquettes/link, <=18 conflicts,
<=14 vertex-sharing neighbours; deterministic greedy 19-packing and
exact incidence separation for selected Wilson one-link conditionals.

Analytic Gibbs conditional factorization and SU(2) Haar tail are PROVED
separately in Docs/physics/YMClayOriginalWilsonCoherentConnectedPolymerPacking20261109.md;
this script alone is NOT an Agda proof or the Clay mass gap.
"""
from itertools import combinations, product
from random import Random

DIM = 4

def make_lattice(side):
    points = list(product(range(side), repeat=DIM))
    directions = range(DIM)
    links = [(x,mu) for x in points for mu in directions]
    def shift(x,mu):
        out=list(x)
        out[mu]=(out[mu]+1)%side
        return tuple(out)
    plaquettes={}
    for x in points:
        for mu,nu in combinations(directions,2):
            involved=frozenset([
                (x,mu),(x,nu),
                (shift(x,mu),nu),
                (shift(x,nu),mu)
            ])
            assert len(involved)==4
            plaquettes[(x,mu,nu)]=involved
    incident={ell:set() for ell in links}
    for p,edges in plaquettes.items():
        for ell in edges:
            incident[ell].add(p)
    conflict={ell:set() for ell in links}
    for edges in plaquettes.values():
        for ell in edges:
            conflict[ell].update(edges-{ell})
    endpoint={ell:set() for ell in links}
    outgoing={x:set() for x in points}
    for ell in links:
        x,mu=ell
        outgoing[x].add(ell)
        outgoing[shift(x,mu)].add(ell)
    for ell in links:
        x,mu=ell
        endpoint[ell]=(outgoing[x] | outgoing[shift(x,mu)])-{ell}
    return links,plaquettes,incident,conflict,endpoint

def greedy_subset(marked,conflict):
    remain=set(marked)
    selected=set()
    while remain:
        chosen=min(remain)
        selected.add(chosen)
        remain.discard(chosen)
        remain.difference_update(conflict[chosen])
    return selected

def main():
    rng=Random(369)
    tested=0
    for side in (3,4):
        links,plaquettes,incident,conflict,endpoint=make_lattice(side)
        nlinks=4*side**4
        assert len(links)==nlinks and len(plaquettes)==6*side**4
        assert all(len(incident[l])==6 for l in links)
        assert all(len(conflict[l])==18 for l in links)
        assert all(len(endpoint[l])==14 for l in links)
        for count in (1,2,3,7,19,38,len(links)//4,len(links)):
            for trial in range(7):
                if count==len(links):
                    marked=links
                else:
                    marked=rng.sample(links,count)
                chosen=greedy_subset(marked,conflict)
                assert 19*len(chosen)>=len(marked)
                for a,b in combinations(chosen,2):
                    assert not (incident[a]&incident[b])
                # Conditioned on all other links, each plaquette contains
                # at most ONE chosen link, so the actual Wilson exponent
                # decomposes as a sum of individual one-link terms.
                assert all(len(edges & chosen)<=1
                           for edges in plaquettes.values())
                tested+=1
        print("side",side,"links",len(links),"plaquettes",len(plaquettes),
              "plaquettes/link",6,"conflicts/link",18,
              "endpoint-neighbours",14)
    assert tested==112
    print("PASS:",tested,"marked-set original star-packing/factorization tests")
    print("MATH: coherent-bad-polymer tail q^ceil(n/19) conditional on true Wilson exterior")
    print("OPEN: connected FRUSTRATED-staple supports, original CMP116, E1, D2, N1, G1")

if __name__=="__main__":
    main()
