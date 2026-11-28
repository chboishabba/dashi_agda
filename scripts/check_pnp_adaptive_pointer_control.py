"""Data-dependent indexing can require every source pointer on one run,
yet use only logarithmic workspace. Functional reachability, not general SAT.
"""
from itertools import product
from random import Random


def chase(table,start=0):
    n=len(table);p=start;reads=0
    if not 0<=start<=n:raise ValueError('start')
    # n is an absorbing target, never read a table entry there.
    # Pointers may revisit a vertex. No visited set is used.
    for _ in range(n):
        if p==n:return True,reads
        p=table[p];reads+=1
        if not 0<=p<=n:raise ValueError('pointer')
    return p==n,reads


def reference(table,start=0):
    n=len(table);seen=set();p=start
    while p!=n and p not in seen:
        seen.add(p);p=table[p]
    return p==n


def controls():
    checks=0;reads=0
    for n in range(1,6):
        for table in product(range(n+1),repeat=n):
            for start in range(n+1):
                a,k=chase(table,start);assert a==reference(table,start) and k<=n
                checks+=1;reads+=k
    big=[];rng=Random(3692837)
    for n in (8,32,128,512,2048):
        order=list(range(n));rng.shuffle(order);t=[0]*n
        for x,y in zip(order,order[1:]+[n]):t[x]=y
        assert chase(t,order[0])==(True,n)
        for x in order:
            q=t.copy();q[x]=x
            assert not chase(q,order[0])[0]
        # State p, counter, read value, O(1) flags. This is a word model;
        # each pointer fetch reads log(n+1) bits if converted to bit access.
        b=n.bit_length();big.append(dict(n=n,sensitive_words=n,reads=n,workspace_upper=3*b+4,read_bits=n*b))
    return dict(checks=checks,reads=reads,controls=big)

if __name__=='__main__':print(controls())
