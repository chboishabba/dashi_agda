#!/usr/bin/env python3
"""Exact 26D string massless polarisations, SO24 Hodge 2<->22,
and M24 duad permutation action no-go.

PRIOR ART: SO(24) physical little group and transverse p-form Hodge duality;
ATLAS M24 classes 2A=1^8 2^8 and 2B=2^12, and M24-p276 duads.
Existing original DASHI owners: LeechWeightTwo196608BridgeExact and
OggSSP2BM24DuadPair24AuthorityExact. No source physics is inferred
from matching degree 276. Exact arithmetic / finite combinatorics only.
"""
from itertools import combinations
from math import comb

N=24
PAIRS=tuple(combinations(range(N),2))
assert len(PAIRS)==276

def parity(seq):
    return -1 if sum(seq[i]>seq[j] for i in range(len(seq))
                     for j in range(i+1,len(seq)))%2 else 1

def dual_basis(pair):
    comp=tuple(i for i in range(N) if i not in pair)
    assert len(comp)==22
    return comp,parity(pair+comp)

def act_form(indices,perm):
    mapped=tuple(perm[i] for i in indices)
    return tuple(sorted(mapped)),parity(mapped)

def atlas_classes():
    # Standard ATLAS natural 24-point cycle types, not arbitrary
    # named elements of an independently constructed M24 action.
    a=list(range(N)); b=list(range(N))
    for i in range(0,16,2):a[i],a[i+1]=a[i+1],a[i]
    for i in range(0,24,2):b[i],b[i+1]=b[i+1],b[i]
    c=list(range(N));d=list(range(N))
    for i in range(0,18,3):c[i],c[i+1],c[i+2]=i+1,i+2,i
    for i in range(0,24,3):d[i],d[i+1],d[i+2]=i+1,i+2,i
    return {'2A':tuple(a),'2B':tuple(b),'3A':tuple(c),'3B':tuple(d)}

def verify():
    assert comb(24,2)==comb(24,22)==276
    assert (24*25//2-1,comb(24,2),1)==(299,276,1)
    assert 299+276+1==24**2==576
    assert 24-2==22 and 26-2==24
    assert len(set(dual_basis(p)[0] for p in PAIRS))==276
    assert all(dual_basis(p)[1]*parity(dual_basis(p)[0]+p)==1 for p in PAIRS)
    print('PASS 26D string SO24 physical fields: graviton299 + B2 276 + dilaton1 = 576')
    print('PASS 24D transverse star: signed orthogonal Lambda2(24) -> Lambda22(24) bijection')
    for cls,perm in atlas_classes().items():
        assert sorted(perm)==list(range(N)) and parity(perm)==1
        fixed=sum(perm[i]==i for i in range(N))
        duad_trace=0;wedge_trace=0
        for p in PAIRS:
            im,s=act_form(p,perm)
            if im==p:duad_trace+=1;wedge_trace+=s
            dual,eps=dual_basis(p)
            dim,ds=act_form(dual,perm)
            expected,deps=dual_basis(im)
            assert dim==expected and eps*ds==s*deps
        square=tuple(perm[perm[i]] for i in range(N))
        trace_sq=sum(square[i]==i for i in range(N))
        assert wedge_trace==(fixed*fixed-trace_sq)//2
        # Sym²_0(24) is the graviton 299, with trace
        # (chi(g)^2+chi(g²))/2 - 1; sum of graviton, B and Phi
        # must equal the character chi_(24 tensor 24)=chi_24(g)^2.
        grav_trace=(fixed*fixed+trace_sq)//2-1
        assert grav_trace=={'2A':43,'2B':11,'3A':20,'3B':-1}[cls]
        assert grav_trace+wedge_trace+1==fixed*fixed
        assert duad_trace=={'2A':36,'2B':12,'3A':15,'3B':0}[cls]
        assert wedge_trace=={'2A':20,'2B':-12,'3A':15,'3B':0}[cls]
        print(f'PASS ATLAS M24 {cls}: fixed24={fixed}, duad276 trace={duad_trace}, grav299 trace={grav_trace}, exterior-B276 trace={wedge_trace}; star equivariant')
    print('NO-GO M24 degree-276 DUAD permutation != natural antisymmetric string-B2 M24 module')
    print('BOUNDARY neither M24 duads nor Leech weight-two coordinates imply a physical string VOA')

if __name__=='__main__':verify()
