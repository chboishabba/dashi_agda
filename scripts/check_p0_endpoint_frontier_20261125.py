from fractions import Fraction as Q
from itertools import product
from random import Random
from check_p0_signed_contrast_20261125 import (
    canon, restrict, add, basis, member, coefficient, translation, refine,
    accepts, value, matrix, sector)

ZERO=(Q(0),)*3

def plus(a,b):return tuple(x+y for x,y in zip(a,b))
def rotate(a,z):return tuple(a[(d-z)%3] for d in range(3))
def normalize(key,a):
    F,cols,t,R=key
    while True:
        if () in F:return None
        u=next((c[0] for c in F if len(c)==1),None)
        if u is None:break
        i=abs(u)-1;b=int(u>0);R=tuple(j for j in R if j!=i)
        t=add(t,cols[i][:-1],-b);a=rotate(a,b*cols[i][-1]);F=restrict(F,i,b)
    return (F,cols,t,R),a

def packet(key,a):
    F,cols,t,R=key
    B=basis(cols[i][:-1] for i in R)
    if not member(B,t):return ZERO,ZERO
    J=basis(cols[i] for i in R)
    labels=[z for z in range(3) if member(J,t+(z,))]
    if not labels:return ZERO,ZERO
    C=2**(len(R)-len(B))
    if not F and not any(t) and not any(any(cols[i][:-1]) for i in R):
        H=[1,0,0]
        for i in R:H=[H[z]+H[(z-cols[i][-1])%3] for z in range(3)]
        v=tuple(sum(H[z]*rotate(a,z)[d] for z in range(3)) for d in range(3))
        return v,v
    v=[rotate(a,z) for z in labels]
    return (tuple(C*min(0,*(x[d] for x in v)) for d in range(3)),
            tuple(C*max(0,*(x[d] for x in v)) for d in range(3)))

def shared(roots,eps,budget):
    live={};exact=ZERO;merges=cancel=steps=0
    def push(key,a):
        nonlocal exact,merges,cancel
        v=normalize(key,a)
        if v is None:return
        key,a=v
        if key in live:
            merges+=1;a=plus(live.pop(key),a)
        if not any(a):cancel+=1;return
        lo,hi=packet(key,a)
        if lo==hi:exact=plus(exact,lo)
        else:live[key]=a
    for c in roots:
        if c is None:continue
        F,cols,t,o,R,w,_,_=c
        push((F,cols,t,R),tuple(w*(3*int(d==o)-1) for d in range(3)))
    oldlo=oldhi=None
    while True:
        lo=hi=exact;P={}
        for key,a in live.items():
            x,y=packet(key,a);P[key]=(x,y);lo=plus(lo,x);hi=plus(hi,y)
        if oldlo is not None:
            lo=tuple(max(x,y) for x,y in zip(lo,oldlo));hi=tuple(min(x,y) for x,y in zip(hi,oldhi))
        a,b=lo,hi
        lo=tuple(max(a[d],-sum(b[j] for j in range(3) if j!=d)) for d in range(3))
        hi=tuple(min(b[d],-sum(a[j] for j in range(3) if j!=d)) for d in range(3))
        oldlo,oldhi=lo,hi
        choices=[d for d in range(3) if lo[d]>=-eps]
        if choices or steps>=budget or not live:return lo,hi,choices,steps,merges,cancel
        d=max(range(3),key=lambda j:lo[j]);key=max(live,key=lambda k:(P[k][1][d]-P[k][0][d],max(y-x for x,y in zip(*P[k]))))
        a=live.pop(key);F,cols,t,R=key;i=R[0]
        for bit in (0,1):push((restrict(F,i,bit),cols,add(t,cols[i][:-1],-bit),R[1:]),rotate(a,bit*cols[i][-1]))
        steps+=1

def adversary(m):
    # z first, then a_1..a_m, then b_1..b_m,c_1..c_m,u,v.
    n=3*m+3;z=1;u=n-1;v=n
    F=[(z,-i) for i in range(2,n+1)]
    F.extend((-z,s*u,t*v) for s,t in product((-1,1),repeat=2))
    for i in range(m):
        a=2+i;b=2+m+i;c=2+2*m+i
        F.extend(((a,-b,c),(-a,b,c)))
    return canon(F),n,(0,)*(n-1)+(1,)

def decode_singleton(F,n,A,target,budget):
    # On exactly-one promise, distinct pairs vanish. Probe actual original bits.
    x=[];steps=0
    for i in range(n):
        obs=[int(j==i) for j in range(n)]
        roots=[sector(F,n,A,target,obs,Q(1))]
        _,_,c,t,_,_=shared(roots,Q(1,8*(n+1)),budget);steps+=t
        if not c or c[0] not in (0,1):return None,steps
        x.append(c[0])
    x=tuple(x)
    if not accepts(F,x) or tuple(sum(a*z for a,z in zip(r,x))%3 for r in A)!=tuple(target):return None,steps
    return x,steps

def main():
    # Same unknown source, three offsets; complete signed cancellation without counting.
    F=((1,2),(-1,3));n=3;roots=[]
    for o in range(3):
        c=sector(F,n,[],(),[0,0,0],Q(1));r=list(c);r[3]=o;roots.append(tuple(r))
    a,b,d,steps,merges,cancels=shared(roots,Q(0),0)
    assert a==b==ZERO and d==[0,1,2] and steps==0 and merges==2 and cancels==1
    rng=Random(610);checks=positive=merges=cancels=0;success={0:0,4:0,32:0,4096:0}
    for n in range(1,5):
        for _ in range(12):
            F=canon(tuple((i+1)*rng.choice((-1,1)) for i in rng.sample(range(n),rng.randrange(1,min(n,3)+1))) for _ in range(rng.randrange(6)))
            S=[x for x in product(range(2),repeat=n) if accepts(F,x)];k=rng.randrange(1,4);L=n+2*k-1;eps=Q(1,8*L)
            p=tuple(rng.randrange(3) for _ in range(n+k-1));q=rng.randrange(len(p));e=rng.randrange(k);b=tuple(rng.randrange(3) for _ in range(e))
            for roots,vs in ((coefficient(F,n,k,p[:q]),[value(S,n,k,p[:q]+(d,)) for d in range(3)]),(translation(F,n,k,p,b),[value(S,n,k,p,b+(d,)) for d in range(3)])):
                v=sum(vs)/3;delta=[3*(x-v) for x in vs];positive+=v>Q(1,24)
                for B in success:
                    lo,hi,c,_,m,z=shared(roots,eps,B);assert all(l<=x<=h for l,x,h in zip(lo,delta,hi));assert all(delta[d]>=-eps for d in c);checks+=3;merges+=m;cancels+=z
                    success[B]+=bool(c) and v>Q(1,24)
                    if B==4096:assert c
    # Verify actual singleton decoder on isolated original affine charts, not supplied witnesses.
    decoder_cases=decoder_steps=0
    for n in range(1,6):
        for _ in range(12):
            F=canon(tuple((i+1)*rng.choice((-1,1)) for i in rng.sample(range(n),rng.randrange(1,min(n,3)+1))) for _ in range(rng.randrange(6)))
            A=[[rng.randrange(3) for i in range(n)] for j in range(rng.randrange(1,n+1))]
            H={}
            for x in product(range(2),repeat=n):
                if accepts(F,x):H.setdefault(tuple(sum(a*z for a,z in zip(r,x))%3 for r in A),[]).append(x)
            for target,W in H.items():
                if len(W)!=1:continue
                x,t=decode_singleton(F,n,A,target,4096);assert x==W[0];decoder_cases+=1;decoder_steps+=t
    assert decode_singleton(((1,),(-1,)),1,[],(),4)[0] is None
    controls=[];signature_checks=0
    for m in range(1,7):
        F,n,p=adversary(m);assert matrix(n,1,p)==[[1]+[0]*(n-1)]
        # Check distinct non-unit residuals at the a-cut, without enumerating full witnesses.
        R=restrict(F,0,1);keys=set()
        for a in product(range(2),repeat=m):
            G=R
            for i,b in enumerate(a,1):G=restrict(G,i,b)
            assert all(len(c)>=2 for c in G);keys.add(G)
        assert len(keys)==2**m;signature_checks+=len(keys)
        # Actual old and shared algorithm on positive singleton parent, bounded runs.
        roots=translation(F,n,1,p,());eps=Q(1,8*(n+1));B=2**m-1
        if m<=4:
            S=[x for x in product(range(2),repeat=n) if accepts(F,x)];assert S==[(0,)*n]
            assert value(S,n,1,p)==Q(1,3)
        for focus in (False,True):
            l,h,c,t=refine(roots,eps,B,focus);assert not c and t==B;assert all(x<=y<=z for x,y,z in zip(l,(2,-1,-1),h))
        l,h,c,t,_,_=shared(roots,eps,B);assert not c and t==B;assert all(x<=y<=z for x,y,z in zip(l,(2,-1,-1),h))
        controls.append((m,n,B))
    print(dict(fixtures=48,contrast_checks=checks,positive_parents=positive,certified=success,merges=merges,cancellations=cancels,synthetic_zero_cancellation=1,distinct_cut_residual_checks=signature_checks,adversary_controls=controls,decoded_singletons=decoder_cases,decoder_refinement_steps=decoder_steps))
if __name__=='__main__':main()
