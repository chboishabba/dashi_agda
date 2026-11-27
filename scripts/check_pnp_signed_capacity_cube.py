"""Canonical signed cube transport and complete single-pin floor discovery.

Doubled integer Fourier ledger; original odd-parity capacity domain.
No dense quotient expansion. None denotes inconsistent original demand.
"""
from collections import defaultdict
from itertools import combinations
from check_pnp_affine_normal_components import canon, bits, chart, satisfies
from check_pnp_signed_capacity_square import add, bounds, row_ledger


def restrict_ledger(M,H):
    """Canonical ambient-slot quotient. None is empty, not a zero ledger."""
    H=canon(H)
    if H is None:return None
    Q={}
    for a,c in M.items():
        for r,b in H:
            if a & (1<<(r.bit_length()-1)):
                a^=r
                if b:c=-c
        add(Q,a,c)
    return Q


def pin_floors(M):
    """All supported/collision pin floors, via one sparse pair pass."""
    C=M.get(0,0);S=sum(abs(c) for a,c in M.items() if a)
    modes=sorted((a,c) for a,c in M.items() if a)
    gains=defaultdict(lambda:[0,0])
    for a,c in modes:
        gains[a][0]+=abs(c)+c;gains[a][1]+=abs(c)-c
    for (a,c),(b,d) in combinations(modes,2):
        gains[a^b][int((c>0)==(d>0))]+=2*min(abs(c),abs(d))
    def odd(v):
        l=(v+1)//2
        return l+(l%2==0)
    return {a:tuple(odd(C-S+v) for v in g) for a,g in gains.items()}


def screen(n,R,H,caps,B):
    B.pay('cube_scope',1+(n+1)*(1+len(H)+len(R)))
    assert H==canon(H) and canon(H+tuple((r,1) for r in R))==H
    assert len(R)==len(caps)
    while True:
        d=n-len(H);B.pay('cube_chart',1+n+(1+d)*(1+len(H)))
        u,V=chart(n,H)
        B.pay('cube_origin',1+n+sum(r.bit_count() for r in R))
        if all((r&u).bit_count()<=c for r,c in zip(R,caps)):
            assert satisfies(u,H,());return H,u,'origin'
        B.pay('cube_group',1+sum(r.bit_count() for r in R)*(1+d))
        M=[row_ledger(r,u,V) for r in R]
        if any(bounds(m)[0]>c for m,c in zip(M,caps)):return None,None,'floor'
        free=tuple(j for j in range(n) if j not in {a.bit_length()-1 for a,b in H})
        pins=[]
        for m,c in zip(M,caps):
            if bounds(m)[1]<=c:continue
            s=sum(a!=0 for a in m);B.pay('cube_pair_scan',1+s+s*(s-1)//2)
            for a,(l,h) in sorted(pin_floors(m).items()):
                B.pay('cube_floor_test')
                if l>c and h>c:return None,None,'both_orientations'
                if l>c or h>c:
                    p=sum(1<<free[j] for j in bits(a));pins.append((p,int(l>c)))
        B.pay('cube_pin_join',1+(1+len(H)+len(pins))**2);K=canon(H+tuple(pins))
        if K is None:return None,None,'pin_conflict'
        if K==H:return H,None,'stalled'
        assert len(K)>len(H);H=K
