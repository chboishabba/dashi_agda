from itertools import combinations
from random import Random
from sympy import Poly, symbols, nextprime, factor_list
from sympy.ntheory.modular import crt
X=symbols('X'); rng=Random(369)
fixtures=[(3,tuple(i for i in range(8) if mask>>i&1)) for mask in range(256)]
fixtures += [(16,tuple(sorted(rng.sample(range(1<<16),m)))) for m in range(1,9) for _ in range(5)]
queries=bad=roots=coeffs=0
for n,S in fixtures:
    t=len(S) or 1; count=n*t*(t-1)//2+(n+1)*t+2
    p=2; packets=[]
    for _ in range(count):
        p=int(nextprime(p)); w=[0]*p
        for a in S:w[a%p]^=1
        a=[(v-w[-1])%2 for v in w[:-1]]
        last=(len(S)-sum(a))%2
        recovered=[(v+last)%2 for v in a]+[last]
        assert recovered==w
        R=[i for i,v in enumerate(recovered) if v]
        packets.append((p,R)); queries+=1
    m=max(len(R) for _,R in packets); assert m==len(S)
    good=[(p,R) for p,R in packets if len(R)==m]; bad+=len(packets)-len(good)
    if not m:continue
    ps=[]; rows=[]; modulus=1
    B=1<<((n+1)*t)
    for p,R in good:
        assert len({a%p for a in S})==m
        c=[1]
        for r in R:
            new=[0]*(len(c)+1)
            for j,v in enumerate(c):new[j]=(new[j]-r*v)%p;new[j+1]=(new[j+1]+v)%p
            c=new
        ps.append(p); rows.append(c); modulus*=p
        if modulus>2*B:break
    assert modulus>2*B
    cs=[]
    for j in range(m+1):
        z=int(crt(ps,[row[j] for row in rows])[0]);cs.append(z if 2*z<=modulus else z-modulus);coeffs+=1
    P=Poly.from_list(cs[::-1],X); expected=Poly(1,X)
    for r in S:expected*=Poly(X-r,X)
    assert P==expected
    factors=factor_list(P)[1]; recovered_roots=[]
    for f,e in factors:
        assert f.degree()==1 and e==1
        a,b=map(int,f.all_coeffs());assert b%a==0; recovered_roots.append(-b//a)
    assert tuple(sorted(recovered_roots))==S;roots+=m
print(dict(fixtures=len(fixtures),packets=queries,collision_packets=bad,reconstructed_coefficients=coeffs,roots=roots))
primes=(3,5,7,11,13,17,19,23)
controls=zero_buckets=cnf_checks=0
for mask in range(1,1<<len(primes)):
    ps=[p for i,p in enumerate(primes) if mask>>i&1]
    b=1
    for p in ps:b^=b<<p
    D=sum(ps); n=D.bit_length(); S=[a for a in range(1<<n) if (b>>a)&1]
    assert min(S)==0 and max(S)==D and len(S)%2==0
    for p in ps:
        w=[0]*p
        for a in S:w[a%p]^=1
        assert not any(w); zero_buckets+=p
    # Each forbidden assignment contributes its full-width exclusion clause.
    clauses=[tuple((i+1)*(-1 if a>>i&1 else 1) for i in range(n)) for a in range(1<<n) if not (b>>a)&1]
    for a in range(1<<n):
        assert all(any(bool(a>>(abs(l)-1)&1)==(l>0) for l in c) for c in clauses)==bool((b>>a)&1)
        cnf_checks+=1
    controls+=1
print(dict(neutral_controls=controls,zero_buckets=zero_buckets,cnf_checks=cnf_checks))
