"""Finite actual adaptive suffix collision and disjoint-difference packing.
No assumed fixed query schedule or charge for overlapping alternatives.
"""
from itertools import product
from random import Random
from collections import Counter


def run(graph,x,k,s):
    seen=[]
    for _ in range(k):
        i,a,b=graph[s];seen.append(i);s=b if x[i] else a
    return s,seen


def controls():
    C=Counter()
    for z in range(128):
        r=Random(3692839+z);n=1+z%7;m=2+z%13;g=[(r.randrange(n),r.randrange(m),r.randrange(m)) for _ in range(m)];accept=[r.randrange(2) for _ in g];p=z%6;k=1+z%9
        A=list(product((0,1),repeat=n));P={x:run(g,x,p,0)[0] for x in A};Q={x:run(g,x,k,P[x]) for x in A}
        for x in A:
            end,reads=Q[x];R=set(reads);diff=[]
            for y in A:
                if P[y]!=P[x] or accept[Q[y][0]]==accept[end]:continue
                D={i for i in range(n) if x[i]!=y[i]};assert D&R;diff.append(D);C['collisions']+=1
            used=set();pack=0
            for D in sorted(diff,key=lambda d:(len(d),tuple(sorted(d)))):
                if D&used:continue
                used|=D;pack+=1
            assert pack<=len(R)<=len(reads)<=k
            C['runs']+=1;C['packed']+=pack;C['nonzero']+=pack>0
        C['fixtures']+=1
    # Exponentially many alternatives differing in the SAME deciding
    # coordinate cannot be charged as separate reads. At most one unit.
    n=12;x=(0,)*n;A=[y for y in product((0,1),repeat=n) if y[0]]
    D=[{i for i in range(n) if x[i]!=y[i]} for y in A];assert all(0 in d for d in D)
    return dict(C,overlap=dict(alternatives=len(A),unit_capacity=1,reads=1))

if __name__=='__main__':print(controls())
