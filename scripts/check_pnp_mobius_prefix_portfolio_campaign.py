from check_pnp_mobius_prefix import prefix_portfolio
from itertools import product
from random import Random
from fractions import Fraction as Q
from collections import Counter
s=Counter()
for i in range(512):
    rng=Random(3692824+i);n=1+i%9;r=i%5;R=tuple(range(n));t=tuple(rng.randrange(3) for _ in range(r));o=i%3;w=Q((-1)**i,3**(i%3))
    F=tuple(tuple((j+1)*rng.choice((-1,1)) for j in rng.sample(R,rng.randrange(min(4,n)+1))) for _ in range(i%9));cols=tuple(tuple(rng.randrange(3) for _ in range(r+1)) for j in R);H=[0]*3
    for x in product(range(2),repeat=n):
        if all(any(x[abs(l)-1]==int(l>0) for l in c) for c in F) and tuple(sum(cols[j][a]*x[j] for j in R)%3 for a in range(r))==t:H[(o+sum(cols[j][-1]*x[j] for j in R))%3]+=1
    v=tuple(w*(3*h-sum(H)) for h in H)
    for budget in (32,128,512,2048):
        q=prefix_portfolio(F,cols,t,o,R,w,8,budget,16);s['attempts']+=1
        if q is None:s['refused']+=1;continue
        a,b,st=q;assert st['allocated']<=budget and all(l<=x<=u for l,x,u in zip(a,v,b));s['checks']+=3;s['exact']+=a==b;s['partial']+=a!=b;s['allocations']+=st['attempts'];s['reserved']+=st['allocated']
print(dict(s))
