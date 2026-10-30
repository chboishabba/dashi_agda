#!/usr/bin/env python3
"""Exact #1414 S3→C2 sign / 11=7+4 reflection Fourier acceptance audit.

Uses the committed Agda source tables from a repository CHECKOUT.
Independent integer/F3 enumerations are computational evidence only.
Does NOT certify Agda typechecking, complex monodromy, rational
irreducible representation equivalence, Hatcher geometry, or Monster 3B.
"""
from collections import Counter
from itertools import permutations, product
from pathlib import Path
import re

ROOT = Path(__file__).resolve().parents[1]
BASE = ROOT / "DASHI/Foundations"

def source(name):
    p=BASE / (name + ".agda")
    assert p.exists(), f"missing proof owner: {p}"
    return p.read_text(encoding="utf-8")

def test():
    q = source("PolynomialC3S3TwentySevenOrbitQuotientExact")
    psrc = source("PolynomialVandermondeOrbitParityIntertwinerExact")
    fourier = source("PolynomialC3S3ReflectionParityFourierExact")
    linear = source("PolynomialC3S3ReflectionParityLinearExact")
    character = source("PolynomialS3TwentySevenPermutationCharacterExact")
    sign = source("PolynomialVandermondeOrbitSignCharacterExact")

    T={"low":0,"mid":1,"high":2}
    V=tuple(range(3))
    identity=(0,1,2)
    r=(1,2,0)
    r2=(2,0,1)
    s=(2,1,0)
    group=list(permutations(V))
    c3=[identity,r,r2]
    codes=list(product(V,repeat=3))

    def key(f): return "".join(map(str,f))
    def inv(p): return tuple(p.index(i) for i in V)
    def action(p,f):
        inverse=inv(p)
        return tuple(p[f[inverse[i]]] for i in V)

    pat=r"Base\.tri-(low|mid|high)"
    rx=re.compile(r"^classify11 \("+pat+r" , \("+pat+r" , "+pat+
                  r"\)\) = (\w+)$",re.M)
    classes={}
    for a,b,c,label in rx.findall(q):
        t=(T[a],T[b],T[c])
        assert t not in classes
        classes[t]=label
    assert len(classes)==27
    refl=dict(re.findall(r"^reflectionOn11 (\w+) = (\w+)$",q,re.M))
    merge=dict(re.findall(r"^mergeToSeven (\w+) = Shape\.(\w+)$",q,re.M))
    assert len(refl)==len(merge)==11
    assert len(set(merge.values()))==7

    for x in codes:
        for y in codes:
            assert (classes[x]==classes[y]) == any(x==action(p,y) for p in c3)
        for p in group:
            desired=classes[x] if p in c3 else refl[classes[x]]
            assert classes[action(p,x)]==desired

    counts=[sum(action(p,x)==x for x in codes) for p in group]
    assert counts==[27,3,3,3,3,3],counts
    for i,n in enumerate(counts):
        assert f"fixed{i} = refl" in character
        assert f"≡ {n}" in character
    assert 27+5*3==6*7
    assert 27+3+3==3*11
    assert (7+4+8*2,7+4-8,7-4)==(27,3,3)

    assert len(re.findall(r"^classifyConjugationByParity Shape\.perm\w+",psrc,re.M))==162
    assert len(re.findall(r"^parityHomomorphism Shape\.perm\w+",psrc,re.M))==36

    for lemma in (
        "firstReconstructed","secondReconstructed",
        "evenReconstructed","oddReconstructed",
        "evenSymmetric","oddAntisymmetric",
    ):
        assert len(re.findall(r"^"+lemma+r" Base\.tri-",fourier,re.M))==9
    for lemma in (
        "evenAverageAdditive","oddHalfDifferenceAdditive",
        "positiveReconstructionAdditive","negativeReconstructionAdditive",
    ):
        assert len(re.findall(r"^"+lemma+r" Base\.tri-",linear,re.M))==81
    assert len(re.findall(r"^oddSignIntertwines Shape\.perm",sign,re.M))==24

    neg=lambda x:(-x)%3
    avg=lambda a,b:neg((a+b)%3)
    odd=lambda a,b:neg((a-b)%3)
    def encode(f):
        return ([f[0],avg(f[1],f[2]),f[3],f[4],
                 avg(f[5],f[6]),avg(f[7],f[8]),avg(f[9],f[10])],
                [odd(f[1],f[2]),odd(f[5],f[6]),
                 odd(f[7],f[8]),odd(f[9],f[10])])
    def decode(e,o):
        return [e[0],(e[1]+o[0])%3,(e[1]-o[0])%3,e[2],e[3],
                (e[4]+o[1])%3,(e[4]-o[1])%3,
                (e[5]+o[2])%3,(e[5]-o[2])%3,
                (e[6]+o[3])%3,(e[6]-o[3])%3]
    for n in range(3**11):
        f=[]; t=n
        for _ in range(11): f.append(t%3);t//=3
        e,o=encode(f)
        assert decode(e,o)==f
        reflected=[f[0],f[2],f[1],f[3],f[4],f[6],f[5],
                   f[8],f[7],f[10],f[9]]
        er,orr=encode(reflected)
        assert er==e and orr==[neg(x) for x in o]

    for a,b,c,d in product(V,repeat=4):
        plus=lambda x,y:(x+y)%3
        assert avg(plus(a,c),plus(b,d))==plus(avg(a,b),avg(c,d))
        assert odd(plus(a,c),plus(b,d))==plus(odd(a,b),odd(c,d))
        assert plus(plus(a,c),plus(b,d))==plus(plus(a,b),plus(c,d))
        assert plus(plus(a,c),plus(b,d))==plus(plus(a,b),plus(c,d))

    print("PASS 27 source classifier; 729 C3 equivalences; 162 S3 sign actions")
    print("PASS six actual fixed-point counts",counts)
    print("PASS all 177147 F3^11 fields: 7-even+4-odd invertible and reflection diagonal")
    print("PASS source 36 parity, 54 pair, 324 additive and 24 sign cases")
    print("NOT RUN: Agda kernel compilation, actual external Galois/Spin/Monster proof")

if __name__=="__main__":
    test()
