#!/usr/bin/env python3
"""Independent exact Q8 reference: effective coarse density from all fibres.

Original noncommutative ordered pairs U_j V_j, arbitrary nonfactorized
fine weights, no bare Wilson assumption. NOT Agda or continuous SU(N)
Borel Haar, no 1024-index kernel permutation or physical Clay proof.
"""
from fractions import Fraction as Q
from itertools import product
from random import Random

G=list(product((1,-1),range(4)))
T=(((1,0),(1,1),(1,2),(1,3)),
   ((1,1),(-1,0),(1,3),(-1,2)),
   ((1,2),(-1,3),(-1,0),(1,1)),
   ((1,3),(1,2),(-1,1),(-1,0)))
def mul(a,b):
    s,k=T[a[1]][b[1]]
    return (a[0]*b[0]*s,k)
def inv(a):return (a[0] if a[1]==0 else -a[0],a[1])
def mean(xs):
    xs=list(xs)
    return sum(xs,Q(0))/len(xs)
def reparam(blocks,fibres):
    return tuple(t for i in range(len(blocks))
                 for t in (mul(blocks[i],inv(fibres[i])),fibres[i]))
def blocks_from_fine(links,n):
    return tuple(mul(links[2*i],links[2*i+1]) for i in range(n))

def check(n,seed):
    rng=Random(1000+100*n+seed)
    fine={key:Q(rng.randrange(1,24),rng.randrange(1,21))
          for key in product(G,repeat=2*n)}
    tests={key:Q(rng.randrange(-12,13),rng.randrange(1,19))
           for key in product(G,repeat=n)}
    original=mean(value*tests[blocks_from_fine(key,n)]
                  for key,value in fine.items())
    effective={blocks:mean(fine[reparam(blocks,fibres)]
                           for fibres in product(G,repeat=n))
               for blocks in tests}
    pushed=mean(effective[blocks]*tests[blocks] for blocks in tests)
    assert original==pushed
    assert all(x>0 for x in effective.values())
    assert mean(fine.values())==mean(effective.values())
    return len(fine)

def main():
    cases=0;points=0
    for n,trials in ((0,1),(1,60),(2,18),(3,2)):
        for seed in range(trials):
            points+=check(n,seed)
            cases+=1
    assert mul(mul((1,1),inv((1,2))),(1,2))==(1,1)
    assert mul(mul((1,1),(1,2)),(1,2))!=(1,1)
    print(f"PASS: {cases} nonfactorized exact Q8 all-pair effective density fixtures")
    print(f"PASS: {points} original finite fine-configuration rows")
    print("PASS: same partition, positive effective coarse density, inverse control")
    print("REFERENCE ONLY: kernel; real SU(N) Haar; original 1024-bond decoder; UV/IR open")

if __name__=="__main__": main()
