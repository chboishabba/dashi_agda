#!/usr/bin/env python3
"""Exact three-branch pooled scatter/PSD seam check (synthetic rational data).

The 369/pants 1→3 branch count is a useful indexing correspondence.
It does NOT establish source identity, covariance gluing, a TQFT,
or a statistical MP null. The two between-group rank-one terms are
essential and are verified here for the same actually pooled rows.
"""
from fractions import Fraction as Q
from random import Random

def mean(rows):
    n, p = len(rows), len(rows[0])
    return [sum((r[j] for r in rows), Q(0))/n for j in range(p)]

def scatter(rows):
    m = mean(rows)
    p = len(m)
    return [[sum(((r[i]-m[i])*(r[j]-m[j]) for r in rows), Q(0))
             for j in range(p)] for i in range(p)]

def triple_glue(groups):
    A, B, C = groups
    a, b, c = len(A), len(B), len(C)
    ma, mb, mc = (mean(g) for g in groups)
    mab = [(a*ma[j]+b*mb[j])/Q(a+b) for j in range(len(ma))]
    d1 = [ma[j]-mb[j] for j in range(len(ma))]
    d2 = [mab[j]-mc[j] for j in range(len(ma))]
    w1 = Q(a*b,a+b)
    w2 = Q((a+b)*c,a+b+c)
    s1, s2, s3 = [scatter(g) for g in groups]
    p = len(ma)
    predicted = [[s1[i][j]+s2[i][j]+s3[i][j]
                  + w1*d1[i]*d1[j] + w2*d2[i]*d2[j]
                  for j in range(p)] for i in range(p)]
    actual = scatter(A+B+C)
    assert predicted == actual
    assert w1 >= 0 and w2 >= 0
    return actual,w1,w2

def tests():
    rng = Random(36927)
    passed = 0
    for p in range(1,6):
        for a in range(1,5):
            for b in range(1,5):
                for c in range(1,5):
                    groups = [[[Q(rng.randrange(-9,10)) for _ in range(p)]
                               for _ in range(n)] for n in (a,b,c)]
                    S,w1,w2 = triple_glue(groups)
                    flat = sum(groups, [])
                    m = mean(flat)
                    assert S == [[sum(((row[i]-m[i])*(row[j]-m[j])
                                       for row in flat),Q(0))
                                   for j in range(p)] for i in range(p)]
                    passed += 1
    assert passed == 320
    return passed

if __name__ == "__main__":
    print(f"PASS {tests()} exact-rational three-branch pooled scatter identities")
