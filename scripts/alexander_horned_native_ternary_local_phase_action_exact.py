#!/usr/bin/env python3
"""Finite exact oracle for original #1244 native balanced-ternary local C3 actions.

Group actions are on address *fields*, not Hatcher's wild exterior pi1.
Classical original group roots: finite direct/semidirect products, permutation
wreath products (Kaloujnine-Krasner 1950-51). New repository Python adapter:
Johl Brown-directed, ChatGPT-assisted (28 October 2026).
No Agda kernel verification or physical/Monster/Spin same-object certificate.
"""
from itertools import product
from random import Random

TRITS=(-1,0,1)
SECTORS=(0,1,2)

def addresses(depth):
    if type(depth) is not int or not 0 <= depth <= 5:
        raise ValueError("finite address depth 0..5 required")
    return tuple((sector,word) for sector in SECTORS
                 for word in product(TRITS,repeat=depth))

def parent(address):
    sector,word=address
    if not word:
        raise ValueError("no parent at root")
    return sector,word[:-1]

def child(address):
    sector,word=address
    return sector,word+(-1,)

def rotate_back(address,shift):
    sector,word=address
    return (sector-shift)%3,word

def field_add(f,g):
    assert f.keys()==g.keys()
    return {x:(f[x]+g[x])%3 for x in f}

def field_neg(f):
    return {x:(-v)%3 for x,v in f.items()}

def shift_field(f,shift):
    return {x:f[rotate_back(x,shift)] for x in f}

def pullback(f,depth):
    assert set(f)==set(addresses(depth))
    return {x:f[parent(x)] for x in addresses(depth+1)}

def semidirect_multiply(a,b):
    f,s=a;g,t=b
    return field_add(f,shift_field(g,s)),(s+t)%3

def semidirect_inverse(a):
    f,s=a
    return field_neg(shift_field(f,(-s)%3)),(-s)%3

def semidirect_unit(depth):
    return {x:0 for x in addresses(depth)},0

def sample_field(depth,rng):
    return {x:rng.randrange(3) for x in addresses(depth)}

def novelty_curve(word):
    seen=set();result=[0]
    for v in word:
        seen.add(v)
        result.append(len(seen))
    return tuple(result)

def check():
    """Deterministic exact enumeration and reproducible finite Monte-less samples."""
    assert [len(addresses(i)) for i in range(6)]==[3,9,27,81,243,729]
    assert 3**len(addresses(2))==7625597484987
    assert 3**(len(addresses(2))+1)==22876792454961
    address_cases=0
    for depth in range(4):
        for x in addresses(depth):
            for a,b in product(SECTORS,repeat=2):
                assert rotate_back(rotate_back(x,a),b)==rotate_back(x,(a+b)%3)
                assert rotate_back(x,0)==x
                address_cases+=1
            if depth<3:
                assert parent(child(x))==x
                for sh in SECTORS:
                    assert parent(rotate_back(child(x),sh))==rotate_back(x,sh)
    # All 3^3 local fields at root, all 3*3^3=81 semidirect elements:
    axes=addresses(0)
    fields=[dict(zip(axes,w)) for w in product(SECTORS,repeat=3)]
    elements=[(f,s) for f in fields for s in SECTORS]
    assert len(elements)==81
    unit=semidirect_unit(0)
    for a in elements:
        assert semidirect_multiply(a,unit)==semidirect_multiply(unit,a)==a
        assert semidirect_multiply(a,semidirect_inverse(a))==unit
        assert semidirect_multiply(semidirect_inverse(a),a)==unit
    all_associative=0
    for a in elements:
        for b in elements:
            ab=semidirect_multiply(a,b)
            for c in elements:
                assert semidirect_multiply(ab,c)==semidirect_multiply(
                    a,semidirect_multiply(b,c))
                all_associative+=1
    assert all_associative==81**3==531441
    rng=Random(424242)
    sampled=0
    for n in range(4):
        for _ in range(300):
            f,g,h=(sample_field(n,rng) for i in range(3))
            a,b,c=(f,rng.randrange(3)),(g,rng.randrange(3)),(h,rng.randrange(3))
            u=semidirect_unit(n)
            assert semidirect_multiply(semidirect_multiply(a,b),c)==(
                semidirect_multiply(a,semidirect_multiply(b,c)))
            assert semidirect_multiply(a,u)==semidirect_multiply(u,a)==a
            assert semidirect_multiply(a,semidirect_inverse(a))==u
            assert semidirect_multiply(semidirect_inverse(a),a)==u
            for sh in SECTORS:
                assert shift_field(field_add(f,g),sh)==field_add(
                    shift_field(f,sh),shift_field(g,sh))
                if n<3:
                    assert pullback(shift_field(f,sh),n)==shift_field(
                        pullback(f,n),sh)
            if n<3:
                assert pullback(field_add(f,g),n)==field_add(
                    pullback(f,n),pullback(g,n))
                assert pullback(field_neg(f),n)==field_neg(pullback(f,n))
                assert (pullback(f,n)==pullback(g,n))==(f==g)
                assert all(pullback(f,n)[child(x)]==f[x] for x in addresses(n))
                assert (pullback(semidirect_multiply(a,b)[0],n),
                        semidirect_multiply(a,b)[1])==semidirect_multiply(
                    (pullback(f,n),a[1]),(pullback(g,n),b[1]))
            sampled+=1

    # This witness separates ORIGINAL #1275 diagonal value-S3 observation
    # from local address-dependent translations. No duplicate Heaps carrier.
    x,y,z=addresses(0)
    start={x:0,y:0,z:0}
    pulse={x:0,y:1,z:0}
    before=novelty_curve(tuple(start[k] for k in (x,y,z)))
    after=novelty_curve(tuple(field_add(start,pulse)[k] for k in (x,y,z)))
    assert before==(0,1,1,1) and after==(0,1,2,2)
    assert all(novelty_curve(tuple((start[k]+sh)%3 for k in (x,y,z)))==before
               for sh in SECTORS)
    return {"status":"PASS","address_shift_checks":address_cases,
            "all_81_cubed_associativity_cases":all_associative,
            "higher_depth_group_checks":sampled,
            "depth_two_cells":27,"depth_two_local_group_size":3**27,
            "depth_two_semidirect_size":3**28,
            "no_go":"local gauge can change Heaps while global relabel cannot"}

if __name__=="__main__":
    print(check())
