from itertools import product
from fractions import Fraction as Q
from random import Random
from collections import defaultdict

# CNF literals are signed 1-based indices.  Arithmetic is exact over F3.
def canon(cs):
    a=sorted({tuple(sorted(set(c))) for c in cs if not any(-x in c for x in c)},key=lambda c:(len(c),c))
    out=[]
    for c in a:
        if not any(set(d)<=set(c) for d in out):out.append(c)
    return tuple(out)
def restrict(F,i,b):
    lit=(i+1)*(1 if b else -1)
    return canon(tuple(x for x in c if x!=-lit) for c in F if lit not in c)
def add(a,b):return tuple((x+y)%3 for x,y in zip(a,b))
def sub(a,b):return tuple((x-y)%3 for x,y in zip(a,b))
def scale(a,v):return tuple(a*x%3 for x in v)
def insert(B,c):
    for i,b in sorted(B.items()):c=sub(c,scale(c[i],b))
    if not any(c):return False
    i=next(i for i,x in enumerate(c) if x);B[i]=scale(c[i],c);return True
def member(B,c):
    for i,b in sorted(B.items()):c=sub(c,scale(c[i],b))
    return not any(c)
def cap(F,remaining,cols,target):
    # Propagate actual units before solving the affine relaxation.
    R=set(remaining)
    while True:
        if () in F:return 0
        unit=next((c[0] for c in F if len(c)==1),None)
        if unit is None:break
        i=abs(unit)-1;b=int(unit>0);assert i in R
        R.remove(i);target=sub(target,scale(b,cols[i]));F=restrict(F,i,b)
    B={};free=set()
    for i in sorted(R):
        if not insert(B,cols[i]):free.add(i)
    if not member(B,target):return 0
    # Each free Boolean vector has at most one pivot completion.  Disjoint
    # clauses involving only free variables remove independent patterns.
    used=set();bound=1
    for c in F:
        s={abs(x)-1 for x in c}
        if s<=free and not s&used:
            used|=s;bound*=2**len(s)-1
    return bound*2**len(free-used)

def interval(F,n,rows,target,K,order=None):
    F=canon(F);target=tuple(target);order=list(range(n)) if order is None else order
    cols=[tuple(r[i]%3 for r in rows) for i in range(n)];zero=(0,)*len(target)
    if not cap(F,order,cols,target):return 0,0,0,0
    T={(F,zero):1};lost=0;drops=0;peak=1
    for h,i in enumerate(order):
        U=defaultdict(int)
        for (R,s),m in T.items():
            for b in (0,1):
                NR=restrict(R,i,b);ns=add(s,scale(b,cols[i]));U[NR,ns]+=m
        scores=[]
        for key,m in U.items():
            R,s=key;C=cap(R,order[h+1:],cols,sub(target,s))
            if C:scores.append((m*C,key,m))
        scores.sort(reverse=True);T={key:m for _,key,m in scores[:K]}
        lost+=sum(v for v,_,_ in scores[K:]);drops+=len(scores[K:]);peak=max(peak,len(T))
    lower=T.get(((),target),0)
    return lower,lower+lost,drops,peak

def accepts(F,x):return all(any(x[abs(l)-1]==int(l>0) for l in c) for c in F)
def mat(A,x):return tuple(sum(a*b for a,b in zip(r,x))%3 for r in A)
def pair_source(F,n,A,E=(),target=(),first=None):
    # x bits first, independent y suffix bits afterwards.  Before first
    # difference y=x; at first difference y=1-x.  Preserve original labels.
    y=[];nextvar=n
    for i in range(n):
        if first is not None and i<=first:y.append((i,int(i==first)))
        else:y.append((nextvar,0));nextvar+=1
    F2=list(F)
    for c in F:
        F2.append(tuple((y[abs(l)-1][0]+1)*(1 if (l>0)^bool(y[abs(l)-1][1]) else -1) for l in c))
    rows=[];rhs=[]
    for r in A:
        row=[0]*nextvar;const=0
        for i,a in enumerate(r):
            row[i]+=a;j,flip=y[i];row[j]-=a*(1-2*flip);const-=a*flip
        rows.append(row);rhs.append(-const%3)
    for r,t in zip(E,target):rows.append(list(r)+[0]*(nextvar-n));rhs.append(t)
    return F2,nextvar,rows,tuple(rhs)

def score(a,b,D):return (Q(2*a[0]-b[1],D),Q(2*a[1]-b[0],D))
def certify(I,eps):
    return [i for i in range(3) if 2*I[i][0]-sum(I[j][1] for j in range(3) if j!=i)>=-3*eps]

if __name__=='__main__':
    rng=Random(369);checks=capacity=0;dropped=0;certs=defaultdict(int);promises=0;coeff_checks=0;strict=0;maxpeak=0
    for n in range(1,6):
        for _ in range(18):
            F=canon(tuple((i+1)*rng.choice((-1,1)) for i in rng.sample(range(n),rng.randrange(1,min(n,3)+1))) for _ in range(rng.randrange(6)))
            S=[x for x in product(range(2),repeat=n) if accepts(F,x)]
            k=rng.randrange(1,4);A=[[rng.randrange(3) for i in range(n)] for j in range(k)]
            e=rng.randrange(k);b=tuple(rng.randrange(3) for _ in range(e));D=3**(k-e-1);eps=Q(1,24*(n+2*k-1))
            exact=[];problems=[]
            for z in range(3):
                t=b+(z,);X=[x for x in S if mat(A[:e+1],x)==t];z1=len(X);z2=sum(mat(A,x)==mat(A,y) for x in X for y in S)
                exact.append(Q(2*z1-z2,D));problems.append(((F,n,A[:e+1],t),pair_source(F,n,A,A[:e+1],t),z1,z2))
            parent=sum(exact)/3;promises+=parent>Q(1,24)
            for K in (1,2,4,16,1024):
                I=[]
                for p1,p2,z1,z2 in problems:
                    a=interval(*p1,K);c=interval(*p2,K)
                    assert a[0]<=z1<=a[1] and c[0]<=z2<=c[1];checks+=2;dropped+=a[2]+c[2];maxpeak=max(maxpeak,a[3],c[3]);I.append(score(a,c,D))
                for (lo,hi),val in zip(I,exact):assert lo<=val<=hi
                choices=certify(I,eps)
                for i in choices:assert exact[i]>=parent-eps
                if parent>Q(1,24) and choices:certs[K]+=1
                if K==1024 and parent>Q(1,24):assert choices
                if choices and not any(I[i][0]>=max(I[j][1] for j in range(3) if j!=i)-eps for i in range(3)):strict+=1
            # First-difference paired sector with actual affine parameterization.
            j=rng.randrange(n);p=pair_source(F,n,A,first=j);ex=sum(x[:j]==y[:j] and x[j]!=y[j] and mat(A,x)==mat(A,y) for x in S for y in S)
            for K in (1,4,1024):
                v=interval(*p,K);assert v[0]<=ex<=v[1];coeff_checks+=1
                if K==1024:assert v[:2]==(ex,ex)
    # Tight rank capacity; count is 2^64 with no need to enumerate equality pairs.
    n=64;A=[[int(i==j) for j in range(n)] for i in range(n)];cols=[tuple(r[i] for r in A) for i in range(n)]
    assert cap((),list(range(n)),cols,(0,)*n)==1
    # Unit and disjoint-free-clause capacity improvements.
    assert cap(((1,),(-1,)),[0],[(0,)],(0,))==0
    assert cap(((1,2),(3,4)),list(range(4)),[(0,)]*4,(0,))==9
    # Deliberately broad intervals: average-based certificate succeeds even
    # when no child can be certified within eps of the maximum.
    I=[(Q(3,5),Q(9,10)),(Q(-1),Q(1)),(Q(-1),Q(1,5))]
    assert certify(I,Q(0))==[0]
    print(dict(count_intervals=checks,first_difference_intervals=coeff_checks,positive_parents=promises,certified_by_cap=dict(certs),discarded_keys=dropped,max_retained=maxpeak,strict_average_certificates=strict))
