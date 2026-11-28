from check_pnp_intrinsic_patch import *
from check_pnp_conditional_autarky import project as original,reopen as old_reopen
from random import Random
from collections import Counter

def main():
    C=Counter()
    for i in range(512):
        rng=Random(3692840+i);n=1+i%9
        F=canon(tuple(tuple((j+1)*rng.choice((-1,1)) for j in rng.sample(range(n),rng.randrange(min(n,4)+1))) for _ in range(i%11)))
        D=tuple(rng.sample(range(n),1+i%min(n,4)));rows=tuple(tuple(rng.randrange(3) for _ in range(n)) for _ in range(i%5));t=tuple(rng.randrange(3) for _ in rows)
        P,w=project(F,n,D,1000000,rows);Q,v=original(F,n,D,1000000,rows=rows)
        assert (P is None)==(Q is None)
        C['fixtures']+=1
        if P is None:C['refused']+=1;continue
        assert P['G']==Q['G'] and { (s,P['image'].decode(k)):N for (s,k),(d,N) in P['table'].items()}=={key:N for key,(d,N) in Q['table'].items()}
        for x in product((0,1),repeat=n):
            a,b=reopen(P,x,t),old_reopen(Q,x,t)
            assert (a is None)==(b is None)
            if a:
                y,N=a;assert N==b[1] and accepts(F,y) and tuple(sum(c*v for c,v in zip(row,y))%3 for row in rows)==t
            C['reopen']+=1
        C['tables']+=1;C['keys']+=len(P['table'])
    # Actual systematic Golay rows used by the existing 729 donor, repeated
    # ambient coordinates, four Boolean copies of each basis direction.
    A=((2,0,2,1,1,2),(2,1,1,2,0,2),(2,2,0,2,1,1),(2,2,1,1,2,0),(2,1,2,0,2,1),(0,1,1,1,1,1))
    G=tuple(tuple(int(i==j) for j in range(6))+row for i,row in enumerate(A))
    rows=tuple(tuple(G[i//4][j%12] for i in range(24)) for j in range(96))
    P,w=project((tuple(range(1,25)),),24,range(24),100000000,rows)
    assert P['rank']==6 and len(P['table'])==729
    assert sum(N for _,N in P['table'].values())==2**24-1
    for (s,k),(d,N) in P['table'].items():
        assert N==__import__('math').prod((5,5,6)[a] for a in k)-int(not any(k))
        assert P['image'].encode(P['image'].decode(k))==k
        assert reopen(P,(0,)*24,P['image'].decode(k))[1]==N
    bad=list(P['image'].decode((0,)*6));bad[-1]=1;assert reopen(P,(0,)*24,bad) is None
    assert project((),24,range(24),0,rows)==(None,0)
    print(dict(C,golay=dict(rank=6,ambient=96,keys=729,mass=2**24-1,peak=P['peak'],probes=P['probes'],work=w)))
if __name__=='__main__':main()
