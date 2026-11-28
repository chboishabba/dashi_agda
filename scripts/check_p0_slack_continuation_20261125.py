from itertools import product
from fractions import Fraction as Q
from sympy import symbols, expand

def psi(h): return h*(2-h)
# Source construction: z, two-bit mode u, original x, two free multiplicity bits.
positive_cases=positive_fibres=0
for r in range(1,7):
    M=2**r
    for c in range(M+1):
        nums=[0,0,0]
        for z,u,x in product(range(2),range(4),range(M)):
            h=sum((u==0 and a==0 and ((x<c) if z==0 else (x>=c))) or
                  (u==1 and a==0) or (u==2 and x<M//2 and a<3) or
                  (u==3 and z==1 and x==0 and a==0) for a in range(4))
            nums[(-z)%3]+=psi(h);positive_fibres+=1
        assert nums==[c-M//2,0,M//2-c+1] and sum(nums)==1
        assert [d for d,v in enumerate(nums) if v>0]==([0] if c>M//2 else [2])
        positive_cases+=1
# Ternary label source with [I I 0] Toeplitz; one canonical binary pair per trit.
threshold_cases=threshold_fibres=0
for r in range(1,6):
    M=2**r;w=r+3
    if w%2==0:w+=1
    D=3**w; B=D//12
    assert D%12==3 and B>=M//2 and B+M//2+1<=D
    for c in range(M+1):
        ns=[0,0,0]
        for z,a in product(range(3),range(D)):
            if z==0: ok=a<B-M//2 or (B-M//2<=a<B-M//2+M and a-(B-M//2)<c)
            elif z==1: ok=a<B-M//2+1 or (B-M//2+1<=a<B-M//2+1+M and a-(B-M//2+1)>=c)
            else: ok=a<B
            ns[(-z)%3]+=int(ok);threshold_fibres+=1
        assert ns==[B-M//2+c,B,B+M//2-c+1]
        assert Q(sum(ns),3*D)>Q(1,12)
        assert [d for d,v in enumerate(ns) if Q(v,D)>Q(1,12)]==([0] if c>M//2 else [2])
        threshold_cases+=1
# Check actual rectangular Toeplitz labels and canonical trit lifts.
labels=0
for k in range(1,7):
    for z in product(range(3),repeat=k):
        pairs=[((0,0),(1,0),(1,1))[a] for a in z]
        x=tuple(a for a,b in pairs)+tuple(b for a,b in pairs)+(0,1)
        h=tuple(sum((int(i-j in (0,-k)))*x[j] for j in range(len(x)))%3 for i in range(k))
        assert h==z;labels+=1
# For positive parents, all children have mean <3 and ordered pair moment <5.
# Use independent finite child distributions, exhaustive small carriers.
child_checks=slack_checks=0
L=7;eta=Q(1,384*L)
for counts in product(range(5),repeat=6):
    hs=[counts[i:i+2] for i in (0,2,4)]
    mu=[Q(sum(h),2) for h in hs];nu=[Q(sum(v*(v-1) for v in h),2) for h in hs]
    V=[a-b for a,b in zip(mu,nu)];parent=sum(V)/3
    if parent<=0:continue
    assert all(v>-2 for v in V)
    assert all(a<3 and b<5 for a,b in zip(mu,nu));child_checks+=3
    # All extreme independent relative approximation errors on both moments.
    for signs in product((-1,1),repeat=6):
        est=[mu[i]*(1+signs[2*i]*eta)-nu[i]*(1+signs[2*i+1]*eta) for i in range(3)]
        j=max(range(3),key=lambda i:est[i])
        assert abs(est[j]-V[j])<=Q(1,48*L)
        assert V[j]>=parent-Q(1,24*L);slack_checks+=1
h=symbols('h');assert expand(h-h*(h-1)-h*(2-h))==0
print(dict(positive_cases=positive_cases,positive_fibres=positive_fibres,threshold_cases=threshold_cases,threshold_fibres=threshold_fibres,canonical_labels=labels,child_bounds=child_checks,slack_controls=slack_checks))
