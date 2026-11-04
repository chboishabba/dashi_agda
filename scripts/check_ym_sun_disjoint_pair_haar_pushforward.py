#!/usr/bin/env python3
"""Exact Q8 group Haar and original periodic 4D side4->side2 pair geometry.

Q8 is noncommutative, NOT a compact continuous SU(N) Borel-Haar,
physical Wilson-Gibbs RG, or Agda-kernel acceptance receipt.
"""
from itertools import product
from fractions import Fraction as Q
from random import Random

# Q8: (sign, basis), basis 0=1, 1=i, 2=j, 3=k.
G = list(product((1, -1), range(4)))
basis_product = (
    ((1,0),(1,1),(1,2),(1,3)),
    ((1,1),(-1,0),(1,3),(-1,2)),
    ((1,2),(-1,3),(-1,0),(1,1)),
    ((1,3),(1,2),(-1,1),(-1,0)),
)
def mul(x,y):
    k,z=basis_product[x[1]][y[1]]
    return x[0]*y[0]*k,z

def exact_haar_expect(func, n):
    return Q(sum(func(v) for v in product(G,repeat=n)), 8**n)

def exact_paired_haar_expect(func, n):
    return Q(sum(func(tuple(mul(v[2*j],v[2*j+1]) for j in range(n)))
                 for v in product(G,repeat=2*n)), 8**(2*n))

def geometry():
    points=list(product(range(4),repeat=4))
    all_fine_bonds={(p,a) for p in points for a in range(4)}
    coarse_points=list(product(range(2),repeat=4))
    groups=[]
    for p in coarse_points:
        fine_origin=tuple(2*x for x in p)
        for a in range(4):
            first=(fine_origin,a)
            target=list(fine_origin);target[a]=(target[a]+1)%4
            second=(tuple(target),a)
            groups.append((p,a,first,second))
    selected=[bond for _,_,a,b in groups for bond in (a,b)]
    assert len(all_fine_bonds)==1024
    assert len(groups)==64
    assert len(selected)==128 and len(set(selected))==128
    assert all(bond in all_fine_bonds for bond in selected)
    assert len(all_fine_bonds-set(selected))==896
    assert all(a[0][axis] % 2 == 0 and b[0][axis] % 2 == 1
               for _,axis,a,b in groups)
    assert all(
        tuple((a[0][j]+2*(j==axis))%4 for j in range(4))
        == tuple(2*((p[j]+(j==axis))%2) for j in range(4))
        for p,axis,a,b in groups
    )
    return len(groups),len(selected),len(all_fine_bonds-set(selected))

def run():
    assert mul((1,1),(1,2))==(1,3)
    assert mul((1,2),(1,1))==(-1,3)
    for x in G:
        assert sorted(mul(x,y) for y in G)==sorted(G)
    rng=Random(443445)
    for _ in range(64):
        f={g:rng.randrange(-31,32) for g in G}
        assert Q(sum(f[mul(u,v)] for u in G for v in G),64)==Q(sum(f[g] for g in G),8)
    pair_checks=0
    for n,trials in ((1,4),(2,8),(3,2)):
        for _ in range(trials):
            weights={key:rng.randrange(-9,10) for key in product(G,repeat=n)}
            f=lambda xs:weights[xs]
            assert exact_paired_haar_expect(f,n)==exact_haar_expect(f,n)
            pair_checks+=1
    links,selected,spectators=geometry()
    print('PASS: 64 exact Q8 one-block noncommutative Haar tests')
    print(f'PASS: {pair_checks} exact Q8 disjoint-pair Haar tests (n<=3)')
    print(f'PASS: native side4->side2: {links} coarse bonds, {selected} disjoint ordered fine links, {spectators} spectators')
    print('REFERENCE ONLY: not SU(N) continuous Haar, Agda kernel, Gibbs RG or Clay gap')

if __name__=='__main__':
    run()
