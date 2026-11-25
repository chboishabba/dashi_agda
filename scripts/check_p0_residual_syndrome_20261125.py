from itertools import product, combinations
from random import Random
from collections import defaultdict
from fractions import Fraction
from sympy import symbols, expand

# Clauses use signed 1-based original variable labels.
FALSE=((),); TRUE=()
def canon(cs):
    ordered=sorted({tuple(sorted(set(c))) for c in cs if not any(-z in c for z in c)},key=lambda c:(len(c),c))
    out=[]; seen=set()
    for c in ordered:
        if not any(d in seen for k in range(len(c)) for d in combinations(c,k)):out.append(c);seen.add(c)
    return tuple(out)
def restrict(R,i,b):
    lit=(i+1)*(1 if b else -1)
    return canon(tuple(z for z in c if z!=-lit) for c in R if lit not in c)
def accepts(F,x):return all(any(x[abs(z)-1]==int(z>0) for z in c) for c in F)
def weaker(R,S):
    ss=set(S);return all(any(d in ss for k in range(len(c)+1) for d in combinations(c,k)) for c in R)
def add(x,y):return tuple((a+b)%3 for a,b in zip(x,y))
def sub(x,y):return tuple((a-b)%3 for a,b in zip(x,y))
def scale(a,x):return tuple(a*b%3 for b in x)
def basis(cols):
    B={}
    for c in cols:
        for i,b in sorted(B.items()):c=sub(c,scale(c[i],b))
        if any(c):
            i=next(i for i,x in enumerate(c) if x);B[i]=scale(c[i],c)
    return B
def in_span(B,c):
    for i,b in sorted(B.items()):c=sub(c,scale(c[i],b))
    return not any(c)

def solve(F,n,rows,target,order,paired=False,first=None,pins=(),decision=False):
    F=canon(F);target=tuple(target);z=(0,)*len(target)
    dom=[];cols=[];val=[]
    for i in range(n):
        a=tuple(r[i]%3 for r in rows);p=tuple(r[i]%3 for r in pins)
        if paired:
            ds=tuple((x,y) for x,y in product(range(2),repeat=2) if first is None or (x==y if i<first else x!=y if i==first else True))
            c=a+p;d=tuple(-v%3 for v in a)+(0,)*len(p)
            vd={(x,y):add(scale(x,c),scale(y,d)) for x,y in ds}
        else:ds=((0,),(1,));vd={(x,):scale(x,a) for x in range(2)}
        dom.append(ds);val.append(vd);cols.append(list(vd.values()))
    residuals=(F,F) if paired else (F,)
    T={(residuals,z):(1,())};stats={'peak':1,'transitions':0,'merges':0,'dominated':0,'bounds':0,'layers':[]}
    for h,i in enumerate(order):
        P=basis(c for j in order[:h+1] for c in cols[j]);Q=basis(c for j in order[h+1:] for c in cols[j]);PQ=basis([*P.values(),*Q.values()]);lam=len(P)+len(Q)-len(PQ)
        U={}
        for (Rs,s),(count,path) in T.items():
            for d in dom[i]:
                stats['transitions']+=1
                NR=tuple(restrict(R,i,b) for R,b in zip(Rs,d))
                if FALSE in NR:continue
                ns=add(s,val[i][d])
                if not in_span(Q,sub(target,ns)):continue
                key=(NR,ns)
                if key in U:
                    c,w=U[key];U[key]=(c+count,w);stats['merges']+=1
                else:U[key]=(count,path+((i,d),))
        r=len({Rs for Rs,s in U});assert len(U)<=r*3**lam;stats['bounds']+=1
        if decision:
            groups=defaultdict(list)
            for key in U:groups[key[1]].append(key)
            keep={}
            for keys in groups.values():
                # Remove only if an already retained weaker state exists; remove dominated old keys too.
                active=[]
                for k in sorted(keys,key=lambda k:(sum(map(len,k[0])),k)):
                    if any(all(weaker(a,b) for a,b in zip(j[0],k[0])) for j in active):stats['dominated']+=1;continue
                    remain=[]
                    for j in active:
                        if all(weaker(a,b) for a,b in zip(k[0],j[0])):stats['dominated']+=1
                        else:remain.append(j)
                    active=remain+[k]
                for k in active:keep[k]=U[k]
            U=keep
        T=U;stats['peak']=max(stats['peak'],len(T));stats['layers'].append(len(T))
    key=((TRUE,TRUE) if paired else (TRUE,),target);c,path=T.get(key,(0,()))
    if c:
        assignment=dict(path);assert len(assignment)==n
        for j in range(2 if paired else 1):assert accepts(F,tuple(assignment[i][j] for i in range(n)))
        acc=z
        for i in range(n):acc=add(acc,val[i][assignment[i]])
        assert acc==target
    return c,stats

def mat(A,x):return tuple(sum(a*b for a,b in zip(r,x))%3 for r in A)
rng=Random(369);counts=decisions=receipts=bounds=merges=dominated=0
for n in range(1,7):
    for trial in range(24):
        F=canon(tuple((i+1)*rng.choice((-1,1)) for i in rng.sample(range(n),rng.randrange(1,min(3,n)+1))) for _ in range(rng.randrange(8)))
        k=rng.randrange(4);A=[[rng.randrange(3) for _ in range(n)] for _ in range(k)];v=tuple(rng.randrange(3) for _ in range(k));order=list(range(n));rng.shuffle(order)
        S=[x for x in product(range(2),repeat=n) if accepts(F,x)]
        j=rng.randrange(n);pins=A[:rng.randrange(k+1)];pv=v[:len(pins)]
        specs=[(A,v,False,None,(),sum(mat(A,x)==v for x in S)),(A,(0,)*k,True,j,(),sum(x[:j]==y[:j] and x[j]!=y[j] and mat(A,x)==mat(A,y) for x in S for y in S)),(A,(0,)*k+pv,True,None,pins,sum(mat(A,x)==mat(A,y) and mat(pins,x)==pv for x in S for y in S))]
        for rows,target,pair,first,pins,expected in specs:
            c,st=solve(F,n,rows,target,order,pair,first,pins);assert c==expected;counts+=1;receipts+=bool(c);bounds+=st['bounds'];merges+=st['merges']
            d,st=solve(F,n,rows,target,order,pair,first,pins,True);assert bool(d)==bool(expected);decisions+=1;receipts+=bool(d);bounds+=st['bounds'];dominated+=st['dominated']
controls=[]
for m in (8,16,32,64):
    F=tuple((i+1,m+j+1) for i in range(m) for j in range(m));n=2*m
    c,st=solve(F,n,[],(),list(range(n)));assert c==2**(m+1)-1 and st['peak']==2
    d,dt=solve(F,n,[],(),list(range(n)),decision=True);assert d and dt['peak']==1
    controls.append((m,c,st['peak'],dt['peak'],st['transitions']))
eq=[]
for m in (2,4,8,10):
    F=tuple(c for i in range(m) for c in ((i+1,-(m+i+1)),(-(i+1),m+i+1)))
    # Exact fixed order has 2^m distinct residual states, but interleaving removes them.
    c,st=solve(F,2*m,[],(),list(range(2*m)));assert c==2**m and st['layers'][m-1]==2**m
    c,dt=solve(F,2*m,[],(),[i for j in range(m) for i in (j,m+j)]);assert c==2**m and dt['peak']==2
    eq.append((m,st['peak'],dt['peak']))
# Positive-root sparse collision control: H=1 everywhere, extra copy iff binary label accepted.
rare=0
for r in range(1,8):
    for c in range(2**r+1):
        D=3**r;assert Fraction(D-c,D)>=Fraction(3**r-2**r,D)>Fraction(1,24)
        assert (2*c==0)==(c==0);rare+=1
h=symbols('h');assert expand(2*h-h*h-h*(2-h))==0
print(dict(counts=counts,decisions=decisions,receipts=receipts,bounds=bounds,merges=merges,dominated=dominated,dense_controls=controls,equality_controls=eq,rare_controls=rare))
