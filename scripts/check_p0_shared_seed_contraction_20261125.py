from itertools import product
from random import Random
from fractions import Fraction
from sympy import symbols, expand

rng=Random(369)
def factor(scope, domains, pred):
    scope=tuple(scope)
    return scope,{v:1 for v in product(*(range(domains[x]) for x in scope)) if pred(*v)}

def graph(n,k,clauses,prefix):
    L=n+2*k-1
    domains={('s',i):3 for i in range(L)}
    domains.update({('x',i):2 for i in range(n)})
    fs=[]
    for i,d in enumerate(prefix):
        fs.append(factor([('s',i)],domains,lambda a,d=d:a==d))
    for cl in clauses:
        scope=[('x',i) for i,b in cl]
        fs.append(factor(scope,domains,lambda *a,cl=cl:any(v==b for v,(_,b) in zip(a,cl))))
    for i in range(k):
        for j in range(n+1):domains[('r',i,j)]=3
        fs.append(factor([('r',i,0)],domains,lambda a:a==0))
        for j in range(n):
            fs.append(factor([('r',i,j),('s',i-j+n-1),('x',j),('r',i,j+1)],domains,lambda a,t,x,b:(a+t*x)%3==b))
        fs.append(factor([('r',i,n),('s',n+k-1+i)],domains,lambda a,b:(a+b)%3==0))
    return domains,fs

def duplicate(domains,fs):
    rename=lambda v:v if v[0]=='s' else ('copy',)+v
    ds=dict(domains);ds.update({rename(v):d for v,d in domains.items()})
    return ds,fs+[(tuple(map(rename,s)),t) for s,t in fs]

def eliminate(domains,fs):
    fs=list(fs); left=set(domains); peak=0; work=0
    while left:
        def key(v):
            union={v}
            for s,t in fs:
                if v in s:union.update(s)
            size=1
            for x in union:size*=domains[x]
            return size,str(v)
        v=min(left,key=key);left.remove(v)
        hit=[(s,t) for s,t in fs if v in s];fs=[(s,t) for s,t in fs if v not in s]
        scope=tuple(sorted({v}|{x for s,t in hit for x in s},key=str)); pos={x:i for i,x in enumerate(scope)}
        rest=tuple(x for x in scope if x!=v); idx=[pos[x] for x in rest]
        lookup=[(tuple(pos[x] for x in s),t) for s,t in hit]; out={}; rows=1
        for x in scope:rows*=domains[x]
        peak=max(peak,rows);work+=rows
        for vals in product(*(range(domains[x]) for x in scope)):
            a=1
            for ix,t in lookup:
                a*=t.get(tuple(vals[i] for i in ix),0)
                if not a:break
            if a:
                r=tuple(vals[i] for i in idx);out[r]=out.get(r,0)+a
        fs.append((rest,out))
    answer=1
    for s,t in fs:
        assert not s;answer*=t.get((),0)
    return answer,peak,work

def brute(n,k,clauses,prefix):
    L=n+2*k-1; counts=[]
    for tail in product(range(3),repeat=L-len(prefix)):
        s=prefix+tail;h=0
        for x in product(range(2),repeat=n):
            if all(any(x[i]==b for i,b in cl) for cl in clauses) and all((sum(s[i-j+n-1]*x[j] for j in range(n))+s[n+k-1+i])%3==0 for i in range(k)):
                h+=1
        counts.append(h)
    return sum(counts),sum(h*h for h in counts),len(counts)

fixtures=0; moments=0; child_checks=0; peak1=peak2=work1=work2=0; different=0
for n in range(1,4):
    for k in (1,2):
        L=n+2*k-1
        for trial in range(6):
            clauses=[]
            for _ in range(rng.randrange(5)):
                ix=sorted(rng.sample(range(n),rng.randrange(1,n+1)))
                clauses.append(tuple((i,rng.randrange(2)) for i in ix))
            d=rng.randrange(L);p=tuple(rng.randrange(3) for _ in range(d))
            scores=[]
            for u in [p]+[p+(a,) for a in range(3)]:
                ds,fs=graph(n,k,clauses,u)
                z1,b1,w1=eliminate(ds,fs);z2,b2,w2=eliminate(*duplicate(ds,fs))
                a,b,D=brute(n,k,clauses,u)
                assert (z1,z2)==(a,b)
                v=Fraction(2*z1-z2,D);scores.append(v)
                assert z2-z1>=0
                different+=int(z2*D!=z1*z1)
                peak1=max(peak1,b1);peak2=max(peak2,b2);work1+=w1;work2+=w2;moments+=2
            assert scores[0]==sum(scores[1:])/3
            if scores[0]>Fraction(1,24):assert max(scores[1:])>=scores[0]
            child_checks+=1;fixtures+=1
h=symbols('h');assert expand(2*h-h*h-h*(2-h))==0
print(dict(fixtures=fixtures,moment_comparisons=moments,child_checks=child_checks,shared_seed_essential=different,peak_single_rows=peak1,peak_pair_rows=peak2,single_rows_processed=work1,pair_rows_processed=work2))
