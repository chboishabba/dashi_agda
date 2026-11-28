from itertools import product, combinations
from functools import lru_cache
from fractions import Fraction
from sympy import symbols, expand, simplify

n=3
X=tuple(product((0,1),repeat=n))
m,q=symbols('m q')
assert simplify(m/q-m*(m-1)/q**2-m*(q-m+1)/q**2)==0

def rows(k,x):
    L=n+2*k-1
    out=[]
    for i in range(k):
        row=[0]*L
        for j in range(n):row[i-j+n-1]=x[j]
        row[n+k-1+i]=1
        out.append(tuple(row))
    return tuple(out)

@lru_cache(None)
def completions(k,prefix,indices):
    L=n+2*k-1; r=len(prefix); w=L-r
    mat=[]
    for idx in indices:
        for a in rows(k,X[idx]):
            mat.append(list(a[r:])+[-sum(a[j]*prefix[j] for j in range(r))%3])
    rank=0
    for j in range(w):
        piv=next((i for i in range(rank,len(mat)) if mat[i][j]%3),None)
        if piv is None:continue
        mat[rank],mat[piv]=mat[piv],mat[rank]
        inv=pow(mat[rank][j]%3,-1,3)
        mat[rank]=[(v*inv)%3 for v in mat[rank]]
        for i in range(len(mat)):
            if i!=rank:
                a=mat[i][j]%3
                mat[i]=[(v-a*b)%3 for v,b in zip(mat[i],mat[rank])]
        rank+=1
    if any(not any(a[:-1]) and a[-1] for a in mat):return 0
    return 3**(w-rank)

# Independent explicit seed truth masks and prefix scores.
mask_table={}
for k in range(1,n+1):
    L=n+2*k-1
    mask_table[k]=[(s,sum(1<<i for i,x in enumerate(X) if all(sum(a*b for a,b in zip(row,s))%3==0 for row in rows(k,x)))) for s in product(range(3),repeat=L)]

fixtures=queries=steps=approx_steps=0
for mask in range(1,1<<len(X)):
    S=tuple(i for i in range(len(X)) if mask>>i&1); m=len(S)
    k=next(k for k in range(1,n+1) if 3**k>=2*m)
    L=n+2*k-1
    sums={}
    for s,b in mask_table[k]:
        H=(mask&b).bit_count(); v=H*(2-H)
        for i in range(L+1):sums[s[:i]]=sums.get(s[:i],0)+v
    assert Fraction(sums[()],3**L)==Fraction(m,3**k)-Fraction(m*(m-1),3**(2*k))>Fraction(1,12)
    def score(p):
        global queries
        v=sum(completions(k,p,(i,)) for i in S)-2*sum(completions(k,p,(i,j)) for i,j in combinations(S,2))
        assert v==sums[p];queries+=1
        return Fraction(v,3**(L-len(p)))
    for approximate in (False,True):
        p=(); eps=Fraction(1,48*L)
        for _ in range(L):
            children=[p+(d,) for d in range(3)]; vals=[score(c) for c in children]
            assert sum(vals)/3==Fraction(sums[p],3**(L-len(p)))
            estimates=[v+(eps if (sum(c)+mask)%2 else -eps) if approximate else v for c,v in zip(children,vals)]
            j=max(range(3),key=lambda j:estimates[j]);p=children[j]
            if approximate:approx_steps+=1
            else:steps+=1
        assert sums[p]==1
    fixtures+=1

# Strict majority -> compare two final translation scores, with both counts >=2.
comparisons=0
for n0 in range(1,9):
    for c in range(2**n0+1):
        h0=2*c+2; h1=2**n0+2
        assert (h1*(2-h1)>h0*(2-h0))==(c>2**(n0-1))
        comparisons+=1

# Semantic residual OBDD width on empty / singleton support, across all orders.
from itertools import permutations
quotients=0
for w in [None]+list(X):
    for order in permutations(range(n)):
        for d in range(n+1):
            rs=set()
            for p in product((0,1),repeat=d):
                rs.add(tuple(int(w is not None and all(w[i]==v for i,v in zip(order,p+z))) for z in product((0,1),repeat=n-d)))
            assert len(rs)<=2
            quotients+=1
print(dict(fixtures=fixtures,seed_masks=sum(map(len,mask_table.values())),rank_score_checks=queries,exact_steps=steps,approximate_steps=approx_steps,majority_controls=comparisons,quotient_checks=quotients))
