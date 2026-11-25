from itertools import product
from fractions import Fraction
from sympy import symbols, expand

H=symbols('H')
assert expand((2*8*H-8*H**2)/8-H*(2-H))==0
n=3
X=list(product(range(2),repeat=n))
seed_tables={}
for k in range(1,n+1):
    L=n+2*k-1
    seed_tables[k]=[(s,sum(1<<i for i,x in enumerate(X) if all((sum(s[a-j+n-1]*x[j] for j in range(n))+s[n+k-1+a])%3==0 for a in range(k)))) for s in product(range(3),repeat=L)]

def psi(h):return h*(2-h)
steps=threshold_steps=bit_probes=identity_prefixes=paired_checks=0
for mask in range(1<<len(X)):
    S=[x for i,x in enumerate(X) if mask>>i&1]
    for d in range(n+1):
        for prefix in product(range(3),repeat=d):
            count=sum(all((x[j]+b)%3==0 for j,b in enumerate(prefix)) for x in S)
            # With A=I, each viable completion is the unique translation -x.
            completions=sum(1 for tail in product(range(3),repeat=n-d) if sum(all((a+b)%3==0 for a,b in zip(x,prefix+tail)) for x in S)==1)
            assert count==completions
            identity_prefixes+=1
    if not S:continue
    k=next(k for k in range(1,n+1) if 3**k>=2*len(S));L=n+2*k-1
    scores={}
    for s,b in seed_tables[k]:
        h=(mask&b).bit_count(); val=psi(h)
        # Four-corner pairing of U-type tag blocks: baseline (2,0), accepted (0,2).
        # Include trivial summands; dot counts for constant unit tag.
        a=(len(X),2*(len(X)-h),2*h); z=(len(X),2*len(X),0)
        dot=lambda p,q:sum(i*j for i,j in zip(p,q))
        K=dot(a,a)-dot(a,z)-dot(z,a)+dot(z,z)
        diag=8*h
        assert K==8*h*h and 2*diag-K==8*val
        paired_checks+=1
        for d in range(L+1):scores[s[:d]]=scores.get(s[:d],0)+val
    for threshold in (Fraction(0),Fraction(1,12)):
        prefix=();assert Fraction(scores[prefix],3**L)>threshold
        while len(prefix)<L:
            d=len(prefix)+1
            children=[prefix+(v,) for v in range(3)]
            # Deliberately choose first qualifying child, not the maximum.
            prefix=next(c for c in children if Fraction(scores[c],3**(L-d))>threshold)
            if threshold:threshold_steps+=1
            else:steps+=1
        assert scores[prefix]==1
        b=next(b for s,b in seed_tables[k] if s==prefix)
        isolated=[x for i,x in enumerate(X) if mask&b&(1<<i)]
        assert len(isolated)==1
        recovered=[]
        for i in range(n):
            values=[psi(sum((x[i]+a)%3==0 for x in isolated)) for a in range(3)]
            assert Fraction(sum(values),3)==Fraction(1,3)
            a=next(a for a,v in enumerate(values) if v>0)
            recovered.append((-a)%3);bit_probes+=1
        assert tuple(recovered)==isolated[0] and tuple(recovered) in S
# Final-trit positivity implies every child has <=2 witnesses and total <=5.
final_controls=positive_controls=0
for hs in product(range(9),repeat=3):
    final_controls+=1
    if sum(map(psi,hs))>0:
        assert max(hs)<=2 and sum(hs)<=5 and 1 in hs
        positive_controls+=1
print(dict(supports=256,nonempty=255,seed_masks=sum(map(len,seed_tables.values())),positive_steps=steps,threshold_steps=threshold_steps,bit_probes=bit_probes,identity_prefixes=identity_prefixes,paired_score_checks=paired_checks,final_controls=final_controls,positive_final_controls=positive_controls))
