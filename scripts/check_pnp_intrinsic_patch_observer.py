from check_pnp_intrinsic_patch import *
from random import Random
from fractions import Fraction
from collections import Counter

def main():
    C=Counter()
    for i in range(512):
        r=Random(3692841+i);n=1+i%9;R=tuple(j for j in range(n) if r.randrange(3));F=canon(tuple(tuple((j+1)*r.choice((-1,1)) for j in r.sample(R,r.randrange(min(len(R),4)+1))) for _ in range(i%11)))
        m=i%5;cols=tuple(tuple(r.randrange(3) for _ in range(m+1)) for _ in range(n));t=tuple(r.randrange(3) for _ in range(m));o=i%3;w=Fraction((-1)**i,i+1);H=[0]*3
        for bits in product((0,1),repeat=len(R)):
            x=dict(zip(R,bits))
            if accepts(F,x) and tuple(sum(cols[j][k]*x[j] for j in R)%3 for k in range(m))==t:H[(o+sum(cols[j][-1]*x[j] for j in R))%3]+=1
        q=contrast(F,cols,t,o,R,w,1000000);assert q is not None and q[0]==q[1]==tuple(w*(3*h-sum(H)) for h in H)
        C['fixtures']+=1;C['contrasts']+=3
    n=24;F=(tuple(range(1,n+1)),);cols=((1,),)*n
    q=contrast(F,cols,(),0,range(n),Fraction(1),1000000)
    assert q is not None and sum(q[2]['head'])==2**n-1
    assert contrast(F,cols,(),0,range(n),Fraction(1),0) is None
    print(dict(C,large=q[2]))
if __name__=='__main__':main()
