from check_pnp_window_fractran import *
from itertools import product
from random import Random
from collections import Counter
from sympy import prime
from check_pnp_gated_guarded_trace import execute_gated
C=Counter()
for seed in range(512):
    r=Random(3692825+seed);q=1+seed%3;a=1+seed%2;n=1+seed%5
    rules=[(r.randrange(q),r.randrange(a),r.randrange(q),r.randrange(a),r.choice((-1,0,1))) for _ in range(seed%9)]
    W=compile_window(q,a,n,rules);C['tables']+=1
    assert len(W.program)<=2*n*q*a
    for p,i,t in product(range(q),range(n),product(range(a),repeat=n)):
        c=(p,i,t);v=W.encode(*c);assert W.decode(v)==c
        status,c1=source_step(W,c);u,k=raw_step(W,v)
        if status=='halt':assert u is None
        else:
            assert k%2==0;z,j=raw_step(W,u);assert j==k+1
            assert W.decode(z)==c1
        C['one_step']+=1
    c=(r.randrange(q),r.randrange(n),tuple(r.randrange(a) for _ in range(n)));limit=seed%17
    z=c;expected='limit';steps=0
    for _ in range(limit):
        why,y=source_step(W,z)
        if why=='halt':expected='halt';break
        steps+=2;z=y
        if why=='escape':expected='escape';break
    assert replay(W,c,limit)==(expected,z,steps);C['runs']+=1;C[expected]+=1;C['raw_steps']+=steps
    if seed<64:
        P=tuple(int(prime(i+1)) for i in range(W.lanes));prog=fractions(W,P);v=prod(P[i] for i in W.encode(*c));initial=v
        for _ in range(2*limit):
            f=next((f for f in prog if v%f.denominator==0),None)
            if f is None:break
            v=v//f.denominator*f.numerator
        V,_,stats=execute_gated(dense_rules(W),tuple(int(i in W.encode(*c)) for i in range(W.lanes)),2*limit)
        assert prod(p**e for p,e in zip(P,V))==v
        assert W.decode(frozenset(i for i,e in enumerate(V) if e))==z
        C['integer_and_gated']+=1
print(dict(C))
