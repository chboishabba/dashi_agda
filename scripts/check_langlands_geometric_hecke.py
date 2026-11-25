"""Original lattice modification and finite parabolic fibre, not a Bun_G sheaf theorem."""
from itertools import combinations, product
from functools import lru_cache
from collections import Counter
import sympy as s

p=3
@lru_cache(None)
def gb(n,k):
    if k<0 or k>n:return 0
    if k==0 or k==n:return 1
    return gb(n-1,k-1)+p**k*gb(n-1,k)

def rrefs(n,d):
    for piv in combinations(range(n),d):
        free=[(i,j) for i,h in enumerate(piv) for j in range(h+1,n) if j not in piv]
        for vals in product(range(p),repeat=len(free)):
            W=s.zeros(d,n)
            for i,h in enumerate(piv):W[i,h]=1
            for (i,j),v in zip(free,vals):W[i,j]=v
            yield W,piv

def rank3(M):
    a=[[int(x)%3 for x in M.row(i)] for i in range(M.rows)];r=0
    for j in range(M.cols):
        h=next((i for i in range(r,len(a)) if a[i][j]),None)
        if h is None:continue
        a[r],a[h]=a[h],a[r];a[r]=[(x*a[r][j])%3 for x in a[r]]
        for i in range(r+1,len(a)):
            t=a[i][j];a[i]=[(x-t*y)%3 for x,y in zip(a[i],a[r])]
        r+=1
    return r

def basis(W,piv):
    n=W.cols
    return s.Matrix.hstack(W.T,*[p*s.eye(n)[:,j] for j in range(n) if j not in piv])

# Literal lattice and reverse basis, not just scalar index. Exhaust all small charts.
charts=0;fibre_tests=0
for n in range(1,5):
    for d in range(n+1):
        hist={r:Counter() for r in range(n+1)};count=0
        for W,piv in rrefs(n,d):
            C=basis(W,piv);D=p*C.inv()
            assert abs(C.det())==p**(n-d) and all(x.q==1 for x in D)
            assert C*D==D*C==p*s.eye(n) and rank3(C)==d
            for r in hist:
                b=rank3(W[:,r:]);a=d-b
                hist[r][a,b]+=1
            charts+=1;count+=1
        assert count==gb(n,d)
        for r,H in hist.items():
            for a in range(r+1):
                b=d-a
                if 0<=b<=n-r:
                    assert H[a,b]==gb(r,a)*gb(n-r,b)*p**(b*(r-a));fibre_tests+=1
# Original rank8 supporting cyclic lattice, with all split sizes and minuscule degrees.
B=s.Matrix([[6,21],[-7,-15]])/9;T=s.diag(*[B]*4)/3
for i in range(3):T[2*i+2:2*i+4,2*i:2*i+2]=s.eye(2)/3
L=s.Matrix.hstack(*[T**i*s.eye(8)[:,0] for i in range(8)])
assert L.det()!=0
checks=0;rank8=0
for r in range(9):
    t=8-r
    for k in range(9):
        total=0
        for i in range(r+1):
            j=k-i
            if not 0<=j<=t:continue
            a,b=r-i,t-j
            total+=gb(r,a)*gb(t,b)*p**(b*i)
            # Twice the normalization exponent, including modulus delta_P^{1/2}.
            assert 2*b*i-k*(8-k)+i*(r-i)+j*(t-j)-i*t+j*r==0
            # One nontrivial graph representative for every dimension pair.
            piv=tuple(range(a))+tuple(range(r,r+b));W=s.zeros(a+b,8)
            for h,c in enumerate(piv):W[h,c]=1
            # graph entries may precede a B pivot: use the same direct basis,
            # not the RREF enumerator. The pivot-column submatrix is identity.
            for h in range(b):
                for c in range(a,r):W[a+h,c]=(h+c+1)%3
            C=basis(W,piv);D=p*C.inv()
            assert abs(C.det())==p**k and all(x.q==1 for x in D)
            assert L*C*D==p*L and rank3(W[:,r:])==b and rank3(W)==a+b
            assert rank3(C)==a+b
            checks+=1;rank8+=1
        assert total==gb(8,k)
print('small original lattice charts',charts,'parabolic count comparisons',fibre_tests)
print('rank8 original lattice and normalization controls',rank8,'split-degree totals',81)
print('rank8 minuscule multiplicities',[gb(8,k) for k in range(9)])
