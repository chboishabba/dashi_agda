"""Exact finite tests of source-unit refinement; no SAT lower bound claim."""
from itertools import product
from random import Random
from math import ceil, log2
from sympy import symbols, expand

rng = Random(369)
counts = dict(instances=0, states=0, edges=0, gains=0, surviving_losses=0,
              localization=0, closure=0, complete=0, hidden=0)

def check(n, table, choices, pins, leaves, completions, edges):
    F = lambda x: (table >> leaves.index(x)) & 1
    A = {p: choices[p] for p in pins}
    S = {p: F(A[p]) for p in pins}
    H = {p: any(F(x) for x in completions[p]) for p in pins}
    assert all(S[p] <= H[p] for p in pins)
    assert all(S[p] == H[p] for p in pins if -1 not in p)
    gains = []
    for p, q, i, b in edges:
        x, y = A[p], A[q]
        retained = S[p] * int(x[i] == b)
        loss = S[p] - retained
        reroute = S[q] - retained
        assert S[q] - S[p] == -loss + reroute
        if not S[p] and S[q]:
            assert F(y) and y in completions[p]
            gains.append((p,q)); counts['gains'] += 1
        if retained and not S[q]:
            assert F(x) and x in completions[q]
            counts['surviving_losses'] += 1
        counts['edges'] += 1
    assert (not gains) == all(S[p] == H[p] for p in pins)
    counts['complete'] += int(not gains)
    for p in pins:
        if H[p] and not S[p]:
            x = next(x for x in completions[p] if F(x))
            path = [p]
            for i, b in enumerate(x):
                if p[i] == -1:
                    q = list(path[-1]); q[i] = b; path.append(tuple(q))
            l,r = 0,len(path)-1; calls = 0
            assert S[path[l]] == 0 and S[path[r]] == 1
            while r-l>1:
                mid=(l+r)//2; calls+=1
                if S[path[mid]]: r=mid
                else: l=mid
            assert (path[l],path[r]) in gains
            assert calls <= ceil(log2(len(path)-1))
            counts['localization'] += 1
            if not any(S[q] for u,q,_,_ in edges if u==p): counts['hidden'] += 1
    C = S.copy()
    for _ in range(n):
        N = C.copy()
        for p,q,_,_ in edges: N[p] |= C[q]
        C = N
    assert all(C[p] == H[p] for p in pins)
    counts['closure'] += len(pins)
    counts['instances'] += 1; counts['states'] += len(pins)

for n in (2,3):
    leaves = list(product((0,1),repeat=n))
    pins = list(product((-1,0,1),repeat=n))
    completions = {p:[x for x in leaves if all(a==-1 or a==b for a,b in zip(p,x))] for p in pins}
    edges=[]
    for p in pins:
        for i,a in enumerate(p):
            if a==-1:
                for b in (0,1):
                    q=list(p);q[i]=b;edges.append((p,tuple(q),i,b))
    for table in range(1<<len(leaves)):
        if n==2:
            for xs in product(*(completions[p] for p in pins)):
                check(n,table,dict(zip(pins,xs)),pins,leaves,completions,edges)
        else:
            for _ in range(16):
                check(n,table,{p:rng.choice(completions[p]) for p in pins},pins,leaves,completions,edges)
print(counts)
a,b,c=symbols('a b c')
assert expand((c-a)-(-a*(1-b)+(c-a*b))) == 0
print('symbolic transport identity 1/1')
# Exact closure-depth anti-control: F=true, all partial-pin states rejected,
# terminal pin states accepted; any closure of radius k<n still rejects root.
for n in range(1,9):
    S=[int(k==n) for k in range(n+1)]
    for k in range(n+1):
        assert S[0]==int(k==n)
        S=[S[j] | S[min(n,j+1)] for j in range(n+1)]
print('closure-depth anti-controls 8/8')
