"""Finite rectangle mixing on actual scheduled deterministic state runs."""
from random import Random
from itertools import product
from collections import Counter

def trace(schedule,step,init,x,y):
    out=[init]
    for t,p in enumerate(schedule):out.append(step(t,p,x if p else y,out[-1]))
    return tuple(out)

def main():
    C=Counter()
    for i in range(4096):
        rng=Random(3692820+i);A=range(2+i%5);S=range(1+i%4);k=i%9;schedule=tuple(rng.randrange(2) for _ in range(k));table={(t,p,x,s):rng.choice(S) for t,p,x,s in product(range(k),range(2),A,S)}
        step=lambda t,p,x,s:table[t,p,x,s];D={x:trace(schedule,step,0,x,x) for x in A}
        for x,y in product(A,repeat=2):
            C['pairs']+=1
            if D[x]==D[y]:
                assert trace(schedule,step,0,x,y)==D[x];C['collisions']+=1
        C['fixtures']+=1
    # Equality via public alternating bit schedule; state = (bit, ok).
    # Exposes why a handoff bound is not an unrestricted circuit bound.
    for n in range(1,9):
        schedule=(1,0)*n
        def step(t,p,x,s):
            bit,ok=s;z=(x>>(t//2))&1
            return (z,ok) if p else (bit,ok and z==bit)
        for x,y in product(range(2**n),repeat=2):
            assert trace(schedule,step,(0,True),x,y)[-1][1]==(x==y);C['equality_checks']+=1
    print(dict(C))
if __name__=='__main__':main()
