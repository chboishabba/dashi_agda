#!/usr/bin/env python3
"""Exact finite centered-covariance rank/nullity receipts, rational arithmetic.
Observational PNF/economic source identity is not established by this module.
"""
from fractions import Fraction as Q
import json

def rref(a):
    m = [[Q(t) for t in row] for row in a]
    if not m:
        return [], []
    width = len(m[0])
    if any(len(row) != width for row in m):
        raise ValueError("ragged matrix")
    pivots = []
    r = 0
    for j in range(width):
        pivot = next((i for i in range(r,len(m)) if m[i][j] != 0), None)
        if pivot is None:
            continue
        m[r],m[pivot] = m[pivot],m[r]
        leading = m[r][j]
        m[r] = [x/leading for x in m[r]]
        for i in range(len(m)):
            if i != r and m[i][j]:
                q = m[i][j]
                m[i] = [a-q*b for a,b in zip(m[i],m[r])]
        pivots.append(j)
        r += 1
        if r == len(m):
            break
    return m,pivots

def kernel_basis(a,p):
    reduced, pivots = rref(a)
    free = [j for j in range(p) if j not in pivots]
    basis = []
    for j in free:
        v = [Q(0)]*p
        v[j] = Q(1)
        for row,k in enumerate(pivots):
            v[k] = -reduced[row][j]
        basis.append(v)
    return basis

def exact_rank_receipt(raw):
    a = [[Q(v) for v in row] for row in raw]
    n = len(a)
    if n < 2 or not a[0]:
        raise ValueError("n>=2 and p>=1 required")
    p = len(a[0])
    if any(len(row)!=p for row in a):
        raise ValueError("ragged matrix")
    mu = [sum(a[i][j] for i in range(n))/n for j in range(p)]
    x = [[a[i][j]-mu[j] for j in range(p)] for i in range(n)]
    assert all(sum(x[i][j] for i in range(n)) == 0 for j in range(p))
    assert all(x[0][j] == -sum(x[i][j] for i in range(1,n)) for j in range(p))
    cov = [[sum(x[r][i]*x[r][j] for r in range(n))/Q(n-1)
            for j in range(p)] for i in range(p)]
    rank_x = len(rref(x)[1])
    rank_c = len(rref(cov)[1])
    ker = kernel_basis(cov,p)
    assert rank_x == rank_c <= min(p,n-1)
    assert len(ker) == p-rank_c >= max(0,p-n+1)
    assert all(all(sum(cov[i][j]*v[j] for j in range(p)) == 0
                   for i in range(p)) for v in ker)
    if ker:
        assert len(rref(ker)[1]) == len(ker)
    return dict(n=n,p=p,rank_centered=rank_x,rank_covariance=rank_c,
                nullity=len(ker),forced_nullity_lower_bound=max(0,p-n+1),
                independent_kernel_vectors=[[str(x) for x in v] for v in ker],
                exact_arithmetic=True,source_specific_null=False)

def run_tests():
    panels = [
       [[1,2,0,3,4],[4,1,2,0,1],[3,0,5,1,2]],
       [[1,2],[3,4],[5,0],[7,2]],
       [[1,2,3,4],[1,2,3,4]],
       [[1,0,0],[0,1,0],[0,0,1],[1,1,1]],
       [[2,2],[4,4]],
    ]
    result = [exact_rank_receipt(panel) for panel in panels]
    assert [r["nullity"] for r in result] == [3,0,4,0,1]
    return result

if __name__ == "__main__":
    print(json.dumps(run_tests(),indent=2))
