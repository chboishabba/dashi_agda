"""Adaptive query footprint, including arbitrary reuse of cached bits.
Agreement is checked on one actual trace, not on a fixed schedule.
"""
from itertools import product
from random import Random
from collections import Counter

def run(ask,x,k,s):
    seen=[]
    for _ in range(k):
        a=ask(s)
        if a is None:break
        i,zero,one=a;seen.append(i);s=one if x[i] else zero
    return s,tuple(seen)

def main():
    C=Counter()
    for j in range(512):
        r=Random(3692826+j);n=1+j%7;size=1+j%9;k=j%11
        table=tuple(None if r.randrange(5)==0 else (r.randrange(n),r.randrange(size),r.randrange(size)) for _ in range(size));out=tuple(r.randrange(2) for _ in range(size));ask=lambda s:table[s]
        for x in product(range(2),repeat=n):
            s,reads=run(ask,x,k,0);R=set(reads);C['runs']+=1
            assert len(R)<=len(reads)<=k
            # Simultaneously perturb ALL unread coordinates, as well as
            # each individual sensitive-coordinate control.
            y=tuple(a if i in R else 1-a for i,a in enumerate(x));assert run(ask,y,k,0)==(s,reads);C['complement_controls']+=1
            D=set()
            for i in range(n):
                y=x[:i]+(1-x[i],)+x[i+1:];t,T=run(ask,y,k,0)
                if out[s]!=out[t]:D.add(i);assert i in R
                if i not in R:assert (t,T)==(s,reads)
                C['flip_checks']+=1
            assert D<=R;C['sensitive_reads']+=len(D)
    # Parity: every original bit sensitive at every input; sharing the
    # parity accumulator cannot save a fresh read. Equality on its diagonal
    # is sensitive to all 2n independent input coordinates.
    for n in range(1,9):
        for x in product(range(2),repeat=n):
            assert all(sum(x)%2!=sum(x[:i]+(1-x[i],)+x[i+1:])%2 for i in range(n));C['parity_controls']+=n
            z=x+x
            for i in range(2*n):
                y=z[:i]+(1-z[i],)+z[i+1:];assert y[:n]!=y[n:];C['equality_controls']+=1
    print(dict(C))
if __name__=='__main__':main()
