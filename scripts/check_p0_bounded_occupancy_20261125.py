from itertools import product
from fractions import Fraction as Q
from sympy import symbols, expand

# Shared-seed signed moment vs bounded occupancy. Rare spikes on 2 bad children.
spike_cases=leaf_checks=moment_checks=0
for w in (2,4,6,8):
    D=3**w; M=3**(w//2)
    for good in range(3):
        for hidden in (0,D//2,D-1):
            H=[[1+(M if d!=good and a==hidden else 0) for a in range(D)] for d in range(3)]
            vals=[Q(sum(h*(2-h) for h in hs),D) for hs in H]
            occ=[Q(sum(h==1 for h in hs),D) for hs in H]
            assert vals==[int(d==good) for d in range(3)]
            assert sum(vals)/3==Q(1,3)
            assert occ==[1 if d==good else 1-Q(1,D) for d in range(3)]
            assert max(occ)-min(occ)==Q(1,D)
            for hs,v in zip(H,vals):
                mu=Q(sum(hs),D); nu=Q(sum(h*(h-1) for h in hs),D)
                assert mu-nu==v and mu<3 and nu<5
                moment_checks+=1
            leaf_checks+=3*D; spike_cases+=1
# Actual [I I 0] Toeplitz canonical binary lift with arbitrary multiplicity bits ignored.
label_checks=0
for k in range(1,7):
    for digits in product(range(3),repeat=k):
        pairs=[((0,0),(1,0),(1,1))[d] for d in digits]
        for extra in ((0,0),(0,1),(1,0),(1,1)):
            x=tuple(a for a,b in pairs)+tuple(b for a,b in pairs)+extra
            assert tuple(sum(int(i-j in (0,-k))*a for j,a in enumerate(x))%3 for i in range(k))==digits
            label_checks+=1
# Independent bounded singleton indicator descent on all 3-bit supports.
n=3; X=list(product(range(2),repeat=n)); tables={}
for k in range(1,4):
    L=n+2*k-1
    tables[k]=[(s,sum(1<<i for i,x in enumerate(X) if all((sum(s[a-j+n-1]*x[j] for j in range(n))+s[n+k-1+a])%3==0 for a in range(k)))) for s in product(range(3),repeat=L)]
fixtures=steps=bit_probes=0
for mask in range(1,256):
    m=mask.bit_count();k=next(k for k in range(1,4) if 3**k>=2*m);L=n+2*k-1
    counts={}; signed=0
    for s,b in tables[k]:
        h=(b&mask).bit_count();signed+=h*(2-h)
        for j in range(L+1):counts[s[:j]]=counts.get(s[:j],0)+int(h==1)
    assert Q(counts[()],3**L)>=Q(signed,3**L)>Q(1,12)
    p=(); eps=Q(1,48*L)
    while len(p)<L:
        d=len(p)+1; old=Q(counts[p],3**(L-d+1));cs=[p+(i,) for i in range(3)]
        ps=[Q(counts[c],3**(L-d)) for c in cs]
        assert sum(ps)/3==old
        es=[v+(eps if (sum(c)+mask)%2 else -eps) for c,v in zip(cs,ps)]
        j=max(range(3),key=lambda j:es[j]);p=cs[j]
        assert ps[j]>=old-2*eps and ps[j]>Q(1,24);steps+=1
    assert counts[p]==1
    b=next(b for s,b in tables[k] if s==p); ix=(mask&b).bit_length()-1; x=X[ix]
    assert (mask&b).bit_count()==1
    for bit in x:
        v=[int((bit+d)%3==0) for d in range(3)];assert sum(v)==1
        assert v.index(1)==(-bit)%3;bit_probes+=1
    fixtures+=1
M=symbols('M');assert expand((1+M)*(2-(1+M))-(1-M**2))==0
print(dict(spike_cases=spike_cases,leaf_checks=leaf_checks,moment_checks=moment_checks,canonical_label_checks=label_checks,seed_masks=sum(map(len,tables.values())),support_fixtures=fixtures,loss_tolerant_steps=steps,bit_probes=bit_probes))
