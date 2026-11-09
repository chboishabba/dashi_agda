#!/usr/bin/env python3
"""Same source binary N21 first-enabled endpoint/history/certificate payload conservation."""
from random import Random
from itertools import product

def bits(n,pad=0):return tuple(bool((n>>i)&1) for i in range(n.bit_length()+pad))
def width_history(hist):return sum(1+len(v) for v,label in hist)
def width_edges(edges):return sum(len(u)+len(v) for u,v,w in edges)
def capacity(edges,cert,hist):return width_history(hist)+width_edges(edges)+len(cert)
def step(edges,cert,hist,ledger,threshold):
    if not edges:
        return edges,cert,hist,ledger,('accepted' if not cert and ledger>=threshold else 'rejected')
    if len(cert)<2:return edges,cert,hist,ledger,'rejected'
    u,v,w=edges[0];a,b=cert[:2]
    if any(sum((int(t)<<i for i,t in enumerate(u)))==sum((int(t)<<i for i,t in enumerate(x))) and label!=a for x,label in hist):
        return edges,cert,hist,ledger,'rejected'
    if any(sum((int(t)<<i for i,t in enumerate(v)))==sum((int(t)<<i for i,t in enumerate(x))) and label!=b for x,label in hist):
        return edges,cert,hist,ledger,'rejected'
    return edges[1:],cert[2:],((u,a),(v,b))+hist,ledger+(w if a!=b else 0),'active'

def check(edges,cert,threshold):
    hist=();ledger=0;start=capacity(edges,cert,hist);steps=0
    for _ in range(len(edges)+1):
        before=capacity(edges,cert,hist)
        edges,cert,hist,ledger,phase=step(edges,cert,hist,ledger,threshold)
        after=capacity(edges,cert,hist)
        assert before==after==start
        assert width_history(hist)<=start
        steps+=1
        if phase!='active':break
    else:raise AssertionError('edge-count-plus-one fuel exhausted while active')
    return steps

def main():
    cases=0;max_steps=0
    rng=Random(1972)
    for n in range(5):
        vertices=list(range(n))
        edges=[(u,v,1) for u in vertices for v in vertices if u<v]
        for labels in product((False,True),repeat=n):
            for m in range(len(edges)+1):
                chosen=edges[:m]
                word_edges=tuple((bits(u),bits(v),w) for u,v,w in chosen)
                cert=tuple(bit for u,v,w in chosen for bit in (labels[u],labels[v]))
                max_steps=max(max_steps,check(word_edges,cert,1));cases+=1
    for _ in range(45000):
        n=rng.randrange(1,35)
        pairs=[(u,v) for u in range(n) for v in range(u+1,n)]
        chosen=sorted(rng.sample(pairs,min(len(pairs),rng.randrange(15))))
        edges=tuple((bits(u,rng.randrange(3)),bits(v,rng.randrange(3)),rng.randrange(-100000,100000)) for u,v in chosen)
        labels=tuple(bool(rng.getrandbits(1)) for _ in range(n))
        cert=tuple(bit for (u,v),edge in zip(chosen,edges) for bit in (labels[u],labels[v]))
        if rng.randrange(8)==0:cert+=tuple(bool(rng.getrandbits(1)) for _ in range(rng.randrange(1,4)))
        if rng.randrange(8)==0:cert=cert[:rng.randrange(len(cert)+1)]
        max_steps=max(max_steps,check(edges,cert,rng.randrange(1,100000)))
        cases+=1
    print(f'Actual first-enabled binary endpoint/history/cert capacity conservation: {cases:,}/{cases:,} PASS')
    print(f'Max observed steps {max_steps}; source fuel bound m+1 respected')
    print('Finite mirror, not Agda kernel or actual tape allocation/clock.')
if __name__=='__main__':main()
