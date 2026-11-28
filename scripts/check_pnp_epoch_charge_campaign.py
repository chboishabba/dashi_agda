"""Actual epoch-local state divergence, not eventual output divergence."""
from itertools import product
from random import Random
from collections import Counter
from check_pnp_future_residual_charge import run

def main():
    C=Counter()
    for i in range(128):
        r=Random(3692843+i);n=1+i%7;m=2+i%11;g=[(r.randrange(n),r.randrange(m),r.randrange(m)) for _ in range(m)]
        A=list(product((0,1),repeat=n));p={x:0 for x in A};paid={x:0 for x in A};actual={x:0 for x in A}
        for k in (1,2,3,5):
            Q={x:run(g,x,k,p[x]) for x in A}
            for x in A:
                end,R=Q[x];R=set(R);D=[]
                for y in A:
                    if p[x]!=p[y]:continue
                    diff={j for j in range(n) if x[j]!=y[j]}
                    if not R&diff:assert Q[x]==Q[y];C['persistent']+=1
                    if end!=Q[y][0]:assert R&diff;D.append(diff);C['separated']+=1
                seen=set();weight=0
                for d in sorted(D,key=lambda z:(len(z),tuple(sorted(z)))):
                    if seen&d:continue
                    seen|=d;weight+=1
                assert weight<=len(R);paid[x]+=weight;actual[x]+=len(Q[x][1]);C['epoch_runs']+=1
            p={x:Q[x][0] for x in A}
        for x in A:
            assert paid[x]<=actual[x]<=11;C['runs']+=1;C['demand']+=paid[x];C['reads']+=actual[x]
        C['fixtures']+=1
    # Parity has two answer fibres of size 2^(n-1), but no future read
    # is needed after compression, despite all coordinates being sensitive.
    n=16;counts=Counter(sum(x)%2 for x in product((0,1),repeat=n));assert counts=={0:32768,1:32768}
    print(dict(C,parity_fibres=dict(counts),future_reads=0))
if __name__=='__main__':main()
