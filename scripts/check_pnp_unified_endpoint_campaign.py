"""Local endpoint scheduler controls; legacy import separately requires checkout."""
from check_pnp_unified_endpoint import solve,classify,accepts
from check_pnp_binary_support_endpoint import child_bounds
from itertools import product
from random import Random
from collections import Counter

def main():
    n=10**100;a=n+2;b=n-1;m=a+b;d=(3*a-m,3*b-m,-m)
    assert child_bounds(d,d)==((a,b),(a,b),m,m)
    r=Random(3692832);C=Counter()
    for i in range(128):
        n=i%7
        F=tuple(tuple((j+1)*r.choice((-1,1)) for j in r.sample(range(n),r.randrange(min(n,3)+1))) for _ in range(i%10))
        S=[x for x in product(range(2),repeat=n) if accepts(F,x)]
        s,x,rec=solve(F,n,65536,legacy=False)
        assert (s=='WITNESS')==bool(S) and (s!='EMPTY' or not S)
        if x is not None:assert x in S
        C[s]+=1
        s,W,rec=classify(F,n,65536,legacy=False)
        assert s==('EMPTY' if not S else 'SINGLETON' if len(S)==1 else 'MULTIPLE')
        assert all(x in S for x in W);C[s]+=1
    F=((-8,-6,7),(-8,-5,1,4),(-5,-4,1,3),(-4,-1,5,7),(-1,4,6),(2,5,6))
    s,x,rec=solve(F,8,0,legacy=False,direct_options=dict(split_budget=0,cell_options=dict(conditioned=False,component_width=None)))
    assert s=='WITNESS' and [a['status'] for a in rec['attempts']]==['UNKNOWN','WITNESS']
    print(dict(counts=dict(C),forced_fallback=x,integer_100_digit_check=True,legacy_exercised=False))
if __name__=='__main__':main()
