#!/usr/bin/env python3
"""Actual normalized orbit transport: value-S3 words -> native trit C2 sign orbits.

Original owners: #1244 H-invariant native-end orbit classifier, #1275
global value-relabelled equality patterns, classical S3=C3⋊C2 and Stirling.
New translation/normalization audit, Johl Brown-directed/ChatGPT 2026-10-28.
NO identity of probability measures, horn geometry, 2I or Monster 3B.
"""
from itertools import product
from math import comb

def trits(n):
    if type(n) is not int or not 0<=n<=7:
        raise ValueError("bounded finite trit length 0..7")
    return product(range(3),repeat=n)

def rgs(word):
    ids={}
    out=[]
    for value in word:
        if value not in ids:
            ids[value]=len(ids)
        out.append(ids[value])
    return tuple(out)

def relative(word):
    if not word:
        raise ValueError("anchored word must contain at least one label")
    a=word[0]
    return tuple((v-a)%3 for v in word[1:])

def sign_orbit(xs):
    xs=tuple(xs)
    return min(xs,tuple((-v)%3 for v in xs))

def transform(word,shift,sign):
    if shift not in range(3) or sign not in (-1,1):
        raise ValueError("actual S3 affine labels required")
    return tuple((shift+sign*v)%3 for v in word)

def orbit_rank(n):
    return (3**n+1)//2

def stirling_at_most_3(m):
    if type(m) is not int or not 1<=m<=8:
        raise ValueError("positive bounded word length required")
    s1=1
    s2=2**(m-1)-1
    s3=(3**m-3*2**m+3)//6
    return s1+s2+s3

def check():
    outcomes={}
    total=0
    for n in range(8):
        by_partition={}
        by_sign={}
        for tail in trits(n+1):
            total+=1
            partition=rgs(tail)
            signed=sign_orbit(relative(tail))
            old=by_partition.setdefault(partition,signed)
            assert old==signed
            other=by_sign.setdefault(signed,partition)
            assert other==partition
            for shift,sgn in product(range(3),(-1,1)):
                moved=transform(tail,shift,sgn)
                assert sign_orbit(relative(moved))==signed
                assert rgs(moved)==partition
                assert relative(moved)==tuple(
                    ((sgn*v)%3 for v in relative(tail)))
            canonical=(0,)+relative(tail)
            assert transform(tail,(-tail[0])%3,1)==canonical
            assert relative(canonical)==relative(tail)
        orbit_count=orbit_rank(n)
        assert len(by_partition)==len(by_sign)==orbit_count
        assert orbit_count==stirling_at_most_3(n+1)
        outcomes[n]={
            "names":3**(n+1),
            "s3_pattern_classes":len(by_partition),
            "sign_classes":len(by_sign)}
    assert [v["sign_classes"] for v in outcomes.values()]==[
        1,2,5,14,41,122,365,1094]
    return {"status":"PASS","orbit_transport_by_depth":outcomes,
            "named_words_checked":total,
            "full_s3_transform_checks":6*total,
            "genuine_equivalence":"S3 value-word orbits <-> C2 relative-sign orbits"}

if __name__=="__main__":
    print(check())
