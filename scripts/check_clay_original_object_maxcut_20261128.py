#!/usr/bin/env python3
"""Section 22 finite proof-algebra controls; no native or Clay acceptance."""
from fractions import Fraction as F
from itertools import product
from math import factorial
import random

def require(b):
    if not b:
        raise AssertionError("maximum-cut control failed")

def main():
    counts = dict(bsd=0,hodge=0,pnp=0,ym=0,ns=0)
    # B=Z/(2m), C=Z/m, j reduction, i image {0,m}.
    # Local maps are reductions to divisors of m, with compatible j_v.
    for m in range(1,25):
        for d in range(1,m+1):
            if m%d: continue
            S={b for b in range(2*m) if b%(2*d) in (0,d)}
            T={c for c in range(m) if c%d==0}
            require({b%m for b in S}==T)
            require({b for b in S if b%m==0}=={0,m})
            for c in T:
                require({b for b in S if b%m==c}=={c,c+m})
                counts["bsd"]+=1
    # Dual numbers Q[e]/e^2, coordinate e, padding by T.
    for a,b,d in product(range(-3,4),range(-3,4),range(1,9)):
        coeff=(F(a),F(b))
        numerator={d:coeff}
        padded={d+3:coeff}
        require(numerator[d]==padded[d+3])
        require((coeff[0]*0,coeff[0])==(0,F(a)))
        counts["hodge"]+=1
    rng=random.Random(369)
    for n in range(2,7):
        for trial in range(20):
            gates=[(rng.randrange(n+i),rng.randrange(n+i)) for i in range(10)]
            out=rng.randrange(n+10)
            for k in range(11):
                L=sorted({v for g in gates[k:] for v in g if v<n+k}
                         | ({out} if out<n+k else set()))
                for x in product((0,1),repeat=n):
                    full=list(x)
                    for a,b in gates: full.append(full[a]^full[b])
                    sparse={v:full[v] for v in L}
                    for i,(a,b) in enumerate(gates[k:],n+k):
                        sparse[i]=sparse[a]^sparse[b]
                    require(sparse[out]==full[out])
                    counts["pnp"]+=1
    for j in range(101):
        r=F(j,100)
        major=r/(2*(1-r/3))
        require(sum((r**n/F(factorial(n+1)) for n in range(1,25)),F(0))<=major<=F(3,4))
        require(1/(1-major)<=4)
        counts["ym"]+=1
    for nu,a,b in product(range(1,9),range(20),range(20)):
        # a*b <= nu*b^2/4+a^2/nu
        require(a*b<=F(nu*b*b,4)+F(a*a,nu))
        counts["ns"]+=1
    print(counts, "total", sum(counts.values()))

if __name__=="__main__":
    main()
