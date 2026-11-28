#!/usr/bin/env python3
"""Section 21h exact finite original-carrier invariants; not Lean/Agda acceptance."""
from itertools import product
from fractions import Fraction
from sympy import symbols, expand
count=0
h,x,y,t=symbols("h x y t")
for d in range(5):
    mons=[h**(d-i-j)*x**i*y**j for i in range(d+1) for j in range(d-i+1)]
    for idx,mon in enumerate(mons):
        p=(idx+1)*mon
        cone=expand(p.subs({h:t,x:2*t,y:-3*t}))
        dehom=p.subs({h:1,x:2,y:-3})
        assert expand(cone-dehom*t**d)==0
        count+=1
for m in range(1,7):
    for n in range(1,5):
        for choices in product(range(n),repeat=m):
            weights=[Fraction(i+1,m+1) for i in range(m)]
            loads=[sum((weights[i] for i in range(m) if choices[i]==j),Fraction(0)) for j in range(n)]
            assert sum(weights,Fraction(0))==sum(loads,Fraction(0))
            if all(v<=1 for v in loads):
                assert sum(weights,Fraction(0))<=n
            count+=1
print(f"Section 21h exact cone/weighted-capacity checks: {count}/{count} PASS")
