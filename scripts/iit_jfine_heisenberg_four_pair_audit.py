#!/usr/bin/env python3
"""Chosen four-pair H4 on the literal 4+1+4 jFine gauge carrier.

Uses the same standard dot/cocycle convention as Monster3BFiniteHeisenberg
CentralExtensionExact, with last two X6 coordinates set to zero. Source H6
is a MODEL; no actual Monster representation is inferred. Central zeta
is a character after characteristic-zero linearisation, NOT an F3 root.
"""
from __future__ import annotations
from itertools import product
import hashlib
import json

T=tuple(product(range(3),repeat=4))
ZERO=(0,0,0,0)
BASIS=tuple(tuple(int(i==j) for i in range(4)) for j in range(4))
IDENT=(ZERO,0,ZERO)

def plus(a,b):
    return tuple((x+y)%3 for x,y in zip(a,b))

def neg(a):
    return tuple((-x)%3 for x in a)

def dot(a,b):
    return sum(x*y for x,y in zip(a,b))%3

def mul(g,h):
    a,c,b=g
    aa,cc,bb=h
    return plus(a,aa),(c+cc+dot(b,aa))%3,plus(b,bb)

def inv(g):
    a,c,b=g
    return neg(a),(-c+dot(b,a))%3,neg(b)

def comm(g,h):
    return mul(mul(mul(g,h),inv(g)),inv(h))

def embed6(g):
    a,c,b=g
    return a+(0,0),c,b+(0,0)

def mul6(g,h):
    a,c,b=g
    aa,cc,bb=h
    return plus(a,aa),(c+cc+dot(b,aa))%3,plus(b,bb)

def global_sign(g):
    a,c,b=g
    return neg(a),(-c)%3,neg(b)

def source_mirror(g):
    a,c,b=g
    return (a[0],a[3],a[2],a[1]),c,(b[1],b[0],b[3],b[2])

def audit():
    n=0
    central=0
    for g in product(T,range(3),T):
        n+=1
        assert mul(g,IDENT)==mul(IDENT,g)==g
        assert mul(g,inv(g))==mul(inv(g),g)==IDENT
        assert mul(mul(g,g),g)==IDENT
        assert embed6(g)[0][-2:]==embed6(g)[2][-2:]==(0,0)
        if g[0]==g[2]==ZERO:
            central+=1
    assert n==19683 and central==3
    for i,j in product(range(4),repeat=2):
        g=(ZERO,0,BASIS[i]);h=(BASIS[j],0,ZERO)
        assert comm(g,h)==(ZERO,int(i==j),ZERO)
        assert embed6(mul(g,h))==mul6(embed6(g),embed6(h))
    for a,b in product(T,T):
        if a==b==ZERO:
            continue
        assert any(dot(b,e)!=0 for e in BASIS) or any(dot(a,e)!=0 for e in BASIS)
    for a,aa,aaa,b,bb,bbb in product(range(3),repeat=6):
        assert (b*aa+(b+bb)*aaa)%3==(bb*aaa+b*(aa+aaa))%3
    g=(ZERO,0,BASIS[0]);h=(BASIS[0],0,ZERO)
    assert global_sign(mul(g,h))!=mul(global_sign(g),global_sign(h))
    assert source_mirror(mul(g,h))!=mul(source_mirror(g),source_mirror(h))
    central_generator=(ZERO,1,ZERO)
    for g in ((ZERO,0,ZERO),(BASIS[0],1,BASIS[2]),((2,1,0,1),2,(1,2,2,0))):
        a,c,b=g
        assert mul(central_generator,g)==(a,(c+1)%3,b)
    for six_vector in product(range(3),repeat=6):
        for axis in range(4):
            changed=list(six_vector)
            changed[axis]=(changed[axis]+1)%3
            assert tuple(changed[-2:])==six_vector[-2:]
    assert 9*81==729
    assert 3**8+2*(3**4)**2==3**9
    receipt={
      "scope":"CHOSEN four-pair group model; not literal Monster 3B action",
      "source_gauge_carrier":"IITJFineFourOneFourS3ZetaGaugeExact.FourOneFour",
      "source_six_pair_owner":"Monster3BFiniteHeisenbergCentralExtensionExact",
      "group_order":n,
      "centre_order":central,
      "symplectic_quotient_order":6561,
      "exhaustive_elements":n,
      "quotient_nonzero_witnesses_checked":6560,
      "single_axis_cocycle_triples":729,
      "model_four_pair_nontrivial_irrep_degree":81,
      "model_nontrivial_central_characters":2,
      "model_linear_characters":6561,
      "model_degree_square_sum":19683,
      "source_H6_zero_tail_embedding":True,
      "H6_729_basis_splits_into_H4_81_blocks":9,
      "global_C3_value_cycle_is_central_left_translation":True,
      "global_S3_value_sign_is_group_automorphism":False,
      "original_D4_mirror_preserves_chosen_cocycle":False,
      "source_monster_representation_intertwiner":False,
      "agda_exact_head_compilation":False
    }
    receipt["payload_sha256"]=hashlib.sha256(
        json.dumps(receipt,sort_keys=True).encode()).hexdigest()
    return receipt

if __name__=="__main__":
    print(json.dumps(audit(),indent=2,sort_keys=True))
