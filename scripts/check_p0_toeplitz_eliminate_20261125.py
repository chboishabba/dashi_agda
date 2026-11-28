from itertools import product
from fractions import Fraction as Q
from random import Random
from sympy import symbols, expand

# Exact Z[zeta_3], zeta^2=-1-zeta.
Z=(0,0); O=(1,0); ROOT=(O,(0,1),(-1,-1))
def add(a,b):return a[0]+b[0],a[1]+b[1]
def mul(a,b):return a[0]*b[0]-a[1]*b[1],a[0]*b[1]+a[1]*b[0]-a[1]*b[1]
def integer(a):assert a[1]==0;return a[0]
def indicator(scope,pred):
    scope=tuple(scope);return scope,{x:O for x in product(range(2),repeat=len(scope)) if pred(*x)}
def count(variables,fs):
    fs=list(fs);left=set(variables)
    while left:
        def key(v):return len({v}|{x for s,_ in fs if v in s for x in s}),v
        v=min(left,key=key);left.remove(v)
        hit=[(s,t) for s,t in fs if v in s];fs=[(s,t) for s,t in fs if v not in s]
        scope=tuple(sorted({v}|{x for s,_ in hit for x in s}));pos={x:i for i,x in enumerate(scope)}
        rest=tuple(x for x in scope if x!=v);ix=[pos[x] for x in rest];out={}
        for vals in product(range(2),repeat=len(scope)):
            a=O
            for s,t in hit:
                a=mul(a,t.get(tuple(vals[pos[x]] for x in s),Z))
                if a==Z:break
            r=tuple(vals[i] for i in ix);out[r]=add(out.get(r,Z),a)
        fs.append((rest,out))
    ans=O
    for s,t in fs:assert not s;ans=mul(ans,t.get((),Z))
    return ans

def source(clauses,rename):
    return [indicator([rename(i) for i,b in cl],lambda *a,cl=cl:any(v==b for v,(_,b) in zip(a,cl))) for cl in clauses]
def weighted_source(n,clauses,weights):
    return count(range(n),source(clauses,lambda i:i)+[((i,),{(0,):O,(1,):ROOT[w%3]}) for i,w in enumerate(weights)])

def coefficient(n,k,clauses,u):
    p=len(u);m=integer(weighted_source(n,clauses,[0]*n));mu=Q(m,3**k);nu=Q(0);calls=1
    for j in range(n):
        t=min(k,max(0,p-n+1+j))
        y=lambda i:i if i<j else n+i
        vs=set(range(n))|{y(i) for i in range(n)}
        base=source(clauses,lambda i:i)+source(clauses,y)+[indicator((j,y(j)),lambda x,z:x!=z)]
        acc=Z
        for a in product(range(3),repeat=t):
            fs=list(base)
            for i in range(j,n):
                w=sum(a[r]*u[n-1+r-i] for r in range(t))%3
                fs.extend([((i,),{(0,):O,(1,):ROOT[w]}),((y(i),),{(0,):O,(1,):ROOT[-w%3]})])
            acc=add(acc,count(vs,fs));calls+=1
        C=integer(acc);assert C%3**t==0;C//=3**t
        nu+=Q(C,3**(2*k-t))
    return mu,nu,calls

def histogram(n,k,clauses,a):
    chars=list(product(range(3),repeat=k));v={}
    for h in chars:
        weights=[sum(h[r]*a[n-1+r-j] for r in range(k))%3 for j in range(n)]
        v[h]=weighted_source(n,clauses,weights)
    W={}
    for b in chars:
        acc=Z
        for h in chars:acc=add(acc,mul(v[h],ROOT[-sum(x*y for x,y in zip(h,b))%3]))
        val=integer(acc);assert val%3**k==0 and val>=0;W[b]=val//3**k
    return W,len(chars)

def ref_hist(n,k,S,a):
    W={b:0 for b in product(range(3),repeat=k)}
    for x in S:
        b=tuple(sum(a[n-1+i-j]*x[j] for j in range(n))%3 for i in range(k));W[b]+=1
    return W

def ref_coef(n,k,S,u):
    m=0;c=0;D=3**(n+k-1-len(u))
    for tail in product(range(3),repeat=n+k-1-len(u)):
        W=ref_hist(n,k,S,u+tail);m+=sum(W.values());c+=sum(h*(h-1) for h in W.values())
    return Q(m,D*3**k),Q(c,D*3**k)

rng=Random(369);fixtures=prefix_checks=translation_checks=hist_entries=contractions=0
for n in range(1,5):
    for k in range(1,4):
        for trial in range(2):
            clauses=[]
            for _ in range(rng.randrange(6)):
                ids=sorted(rng.sample(range(n),rng.randrange(1,min(3,n)+1)))
                clauses.append(tuple((i,rng.randrange(2)) for i in ids))
            S=[x for x in product(range(2),repeat=n) if all(any(x[i]==b for i,b in cl) for cl in clauses)]
            a=tuple(rng.randrange(3) for _ in range(n+k-1))
            for p in range(len(a)+1):
                mu,nu,calls=coefficient(n,k,clauses,a[:p]);assert (mu,nu)==ref_coef(n,k,S,a[:p]);contractions+=calls;prefix_checks+=1
            W,calls=histogram(n,k,clauses,a);assert W==ref_hist(n,k,S,a);contractions+=calls;hist_entries+=len(W)
            for e in range(k+1):
                for b in product(range(3),repeat=e):
                    vals=[v for h,v in W.items() if tuple(-z%3 for z in h[:e])==b];D=3**(k-e)
                    ref=[v for h,v in ref_hist(n,k,S,a).items() if tuple(-z%3 for z in h[:e])==b]
                    assert (Q(sum(vals),D),Q(sum(v*(v-1) for v in vals),D))==(Q(sum(ref),D),Q(sum(v*(v-1) for v in ref),D));translation_checks+=1
            fixtures+=1
h=symbols('h');assert expand(h-h*(h-1)-h*(2-h))==0
print(dict(fixtures=fixtures,coefficient_prefixes=prefix_checks,translation_prefixes=translation_checks,histogram_entries=hist_entries,source_contractions=contractions))
