from check_pnp_target_trellis import *
from random import Random
from itertools import product
from collections import Counter


def main():
    C=Counter()
    for i in range(256):
        g=Random(3692846+i);r=i%25;B=();rows=[]
        for _ in range(1+i%37):
            a=tuple(g.randrange(3) for _ in range(r));rows.append(a);B=extend_rref(B,a)
            assert B==tuple(row[:-1] for row in rref(tuple(b+(0,) for b in rows),r)[0])
            C['basis_insertions']+=1
    for i in range(512):
        g=Random(3692843+i);n=1+i%9;m=i%5;R=list(range(n));g.shuffle(R);R=tuple(R[:1+i%n]);F=tuple(tuple((j+1)*g.choice((-1,1)) for j in g.sample(R,g.randrange(min(4,len(R))+1))) for _ in range(i%9));cols=tuple(tuple(g.randrange(3) for _ in range(m+1)) for _ in range(n));t=tuple(g.randrange(3) for _ in range(m));o=i%3
        H=[0]*3
        def label(bits):
            x=dict(zip(R,bits))
            if all(any(x[abs(l)-1]==int(l>0) for l in c) for c in F) and tuple(sum(cols[j][k]*x[j] for j in R)%3 for k in range(m))==t:return (o+sum(cols[j][-1]*x[j] for j in R))%3
        for bits in product((0,1),repeat=len(R)):
            a=label(bits)
            if a is not None:H[a]+=1
            C['points']+=1
        q,s=trellis(F,cols,t,o,R,10000000);assert q is not None and q[0]==tuple(H)
        for d,p in enumerate(q[1]):assert (p is not None)==bool(H[d]) and (p is None or label(p)==d)
        C['fixtures']+=1;C['labels']+=3;C['witnesses']+=sum(h>0 for h in H)
    # High global rank, low crossing rank, connected monotone chain.
    n=64;R=tuple(range(2*n));cols=tuple(tuple(int(j==i//2) for j in range(n))+(int(i%2==0),) for i in R);F=tuple((-2*i-1,2*i+3) for i in range(n-1));t=(1,)*n
    q,s=trellis(F,cols,t,0,R,20000000);assert q is not None and sum(q[0])==n+1 and s['rank']==n and s['crossing']==1
    assert q[0]==tuple(sum(i%3==d for i in range(n+1)) for d in range(3))
    assert trellis(F,cols,t,0,R,0)[0] is None
    print(dict(C,chain=dict(s,variables=2*n,mass=sum(q[0]),histogram=q[0])))
if __name__=='__main__':main()
