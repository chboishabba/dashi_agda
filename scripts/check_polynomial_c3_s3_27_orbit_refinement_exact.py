#!/usr/bin/env python3
"""Exact 27-conjugation orbit refinement: C3 versus S3.

Classical permutation conjugation; original DASHI ternary endomorphism
owner and original Vandermonde/discriminant owner are imported by the
new bridge on #1414. This checker does not identify ternary tables with
polynomial roots, an actual wild exterior, or any Monster object.
"""
from itertools import permutations, product
from collections import Counter
from pathlib import Path
import re

points=list(range(3))
S3=list(permutations(points))
identity=(0,1,2)
r=(1,2,0)
r2=(2,0,1)
s=(2,1,0)
C3=(identity,r,r2)
codes=list(product(points,repeat=3))

def inv(p): return tuple(p.index(v) for v in points)
def mul(p,q): return tuple(p[q[x]] for x in points)
def conjugate(p,f):
    ip=inv(p)
    return tuple(p[f[ip[x]]] for x in points)
def partition(group):
    unseen=set(codes)
    blocks=[]
    while unseen:
        f=min(unseen)
        orbit=frozenset(conjugate(p,f) for p in group)
        assert orbit <= unseen
        blocks.append(orbit)
        unseen-=orbit
    return blocks


def verify_checked_out_agda_classifiers():
    """Read the exact source tables, not only a reconstructed Python quotient."""
    src=Path(__file__).resolve().parents[1] / (
        "DASHI/Foundations/PolynomialC3S3TwentySevenOrbitQuotientExact.agda"
    )
    assert src.is_file(), "Run this test from a checkout containing the Agda module"
    text=src.read_text(encoding="utf-8")
    tri={"low":0,"mid":1,"high":2}
    pattern=r"Base\.tri-(low|mid|high)"
    cl=re.compile(r"^classify11 \("+pattern+r" , \("+pattern+r" , "+pattern+
                  r"\)\) = (\w+)$",re.M)
    table={}
    for a,b,c,name in cl.findall(text):
        key=(tri[a],tri[b],tri[c])
        assert key not in table
        table[key]=name
    assert len(table)==27
    reppat=re.compile(r"^representative11 (\w+) = "+pattern+r" , \("+pattern+
                      r" , "+pattern+r"\)$",re.M)
    representatives={name:(tri[a],tri[b],tri[c]) for name,a,b,c in reppat.findall(text)}
    assert len(representatives)==11
    reflpat=re.compile(r"^reflectionOn11 (\w+) = (\w+)$",re.M)
    reflected=dict(reflpat.findall(text))
    assert len(reflected)==11
    mergepat=re.compile(r"^mergeToSeven (\w+) = Shape\.(\w+)$",re.M)
    merge=dict(mergepat.findall(text))
    assert len(merge)==11 and len(set(merge.values()))==7
    for x in codes:
        name=table[x]
        assert table[conjugate(r,x)]==name
        assert reflected[name]==table[conjugate(s,x)]
        assert table[representatives[name]]==name
        for y in codes:
            assert (table[x]==table[y]) == any(
                x==conjugate(p,y) for p in C3)
    assert Counter(table.values()) == Counter({name:len(
        [x for x in codes if table[x]==name]) for name in representatives})
    print("PASS exact Agda classifier table: 27 states × 27 pair tests")
    print("PASS 11 representatives, 11 involution labels and 7 merged shapes")

def main():
    verify_checked_out_agda_classifiers()
    assert len(codes)==27 and len(S3)==6
    assert mul(mul(s,r),s)==r2
    for f in codes:
        assert conjugate(r,conjugate(r,conjugate(r,f)))==f
        assert conjugate(s,conjugate(s,f))==f
        assert conjugate(s,conjugate(r,conjugate(s,f)))==conjugate(r2,f)
    small=partition(C3)
    full=partition(S3)
    assert len(small)==11 and Counter(map(len,small))=={3:8,1:3}
    assert len(full)==7 and Counter(map(len,full))=={6:3,3:2,2:1,1:1}
    splitting=[sum(o <= block for o in small) for block in full]
    assert Counter(splitting)=={2:4,1:3}
    fixed=[f for f in codes if conjugate(r,f)==f]
    assert fixed==[identity,r,r2]
    for roots in product(range(-2,3),repeat=3):
        a,b,c=roots
        V=(a-b)*(a-c)*(b-c)
        for p in S3:
            transformed=tuple(roots[p[x]] for x in range(3))
            x,y,z=transformed
            newV=(x-y)*(x-z)*(y-z)
            inversions=sum(p[i]>p[j] for i in points for j in points if i<j)
            assert newV==((-1)**inversions)*V
            assert newV*newV==V*V
    print("PASS C3 orbit partition: 27 -> 11 (three singleton, eight triple)")
    print("PASS S3 orbit partition: 27 -> 7; four two-to-one merges")
    print("PASS dihedral srs=r^-1 and 27/27 table actions")
    print("PASS Vandermonde parity and discriminant for 125 root triples × 6")
    print("NO CLAIM: root triples equal ternary endomorphisms or wild/Monster objects")

if __name__=="__main__":
    main()
