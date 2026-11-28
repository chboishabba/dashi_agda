"""Rational chart residual values and original factor accumulators.
State equality preserves every future continuation; capped reachable states.
"""
from fractions import Fraction as Q
from check_pnp_boolean_fibre import chart
from check_pnp_source_derived_cover import Reservation,Refused


def solve(A,b,n,F=(),H=(),t=(),O=(),cap=1000000,clip=None,permutation=None,max_states=4096,prune=False):
    if n<0 or len(A)!=len(b) or len(H)!=len(t) or any(len(r)!=n for r in A+H) or any(not 1<=abs(l)<=n for c in F for l in c) or any(len(set(c))!=len(c) or any(not 0<=i<n for i in c) for c in O) or clip not in (None,2) or max_states<1:raise ValueError('source')
    p=tuple(range(n)) if permutation is None else tuple(permutation)
    if len(p)!=n or set(p)!=set(range(n)):raise ValueError('permutation')
    B=Reservation(cap);peak=1;observed_peak=1;steps=0;completed_layers=0;stop=None
    def out(status,**kw):return dict(status=status,used=cap-B.left,peak=peak,observed_peak=observed_peak,completed_layers=completed_layers,stop=stop,steps=steps,**kw)
    def trim(m):return m if clip is None else min(2,m)
    try:
        B.pay(1+n+len(A)*(n+1));z,_=chart(tuple(tuple(r[j] for j in p) for r in A),b,n,B)
        if z is None:return out('EMPTY',count=0)
        J,C0=z;J=tuple(p[j] for j in J);C=[None]*n
        for j,(a,s) in enumerate(C0):C[p[j]]=(a,{p[k]:v for k,v in s.items()})
        pos={j:k for k,j in enumerate(J)};end=[max((pos[k] for k in s),default=-1) for a,s in C];start=[min((pos[k] for k in s),default=-1) for a,s in C]
        bounds={}
        if prune:
            B.pay(1+n*(1+len(J)))
            for i,(a,s) in enumerate(C):
                lo=hi=Q(0)
                for k in reversed(range(len(J))):
                    bounds[i,k]=(lo,hi);c=s.get(J[k],0);lo+=min(0,c);hi+=max(0,c)
        factors=[];uses=[[] for _ in range(n)]
        def add(kind,terms,target):
            i=len(factors);last=max((end[j] for j in terms),default=-1);first=min((end[j] for j in terms),default=-1)
            factors.append((kind,terms,target,first,last))
            for j,c in terms.items():uses[j].append((i,c))
        B.pay(1+n+sum(1+len(c) for c in F+O)+len(H)*(n+1))
        for c in F:
            terms={}
            for l in c:terms[abs(l)-1]=terms.get(abs(l)-1,0)|(1<<int(l>0))
            add('or',terms,1)
        for r,s in zip(H,t):add('f3',{j:v%3 for j,v in enumerate(r) if v%3},s%3)
        for c in O:add('one',{j:1 for j in c},1)
        def update(kind,u,c,v):
            if kind=='or':return int(bool(u or (c>>v&1)))
            if kind=='f3':return (u+c*v)%3
            return u+c*v
        # Constants are resolved before the first free coordinate.
        init={i:0 for i,f in enumerate(factors) if f[3]==-1}
        for j,(a,s) in enumerate(C):
            if not s:
                if a not in (0,1):return out('EMPTY',count=0)
                for i,c in uses[j]:init[i]=update(factors[i][0],init[i],c,int(a))
        if any(init[i]!=f[2] for i,f in enumerate(factors) if f[4]==-1):return out('EMPTY',count=0)
        if any(init[i]>1 for i,f in enumerate(factors) if f[0]=='one' and i in init):return out('EMPTY',count=0)
        prevC=();prevF=tuple(i for i in init if factors[i][4]>=0);D={((),tuple(init[i] for i in prevF)):(1,0)}
        for k,j in enumerate(J):
            B.pay(1+n+len(factors));curC=tuple(i for i in range(n) if start[i]<=k<end[i] and start[i]>=0);finish=tuple(i for i in range(n) if end[i]==k);curF=tuple(i for i,f in enumerate(factors) if f[3]<=k<f[4]);retire=tuple(i for i,f in enumerate(factors) if f[4]==k)
            N={}
            for (ck,fk),(mass,w) in D.items():
                for bit in (0,1):
                    B.pay(1+n+len(factors)+sum(len(uses[i]) for i in finish));steps+=1;cval=dict(zip(prevC,ck));fval=dict(zip(prevF,fk));ok=True
                    def partial(i):return cval.get(i,C[i][0])+C[i][1].get(j,0)*bit
                    for i in finish:
                        v=partial(i)
                        if v not in (0,1):ok=False;break
                        for f,a in uses[i]:
                            fval[f]=update(factors[f][0],fval.get(f,0),a,int(v))
                    if not ok or any(fval.get(i,0)!=factors[i][2] for i in retire) or any(factors[i][0]=='one' and fval.get(i,0)>1 for i in curF):continue
                    cv=tuple(partial(i) for i in curC)
                    if prune:
                        B.pay(1+len(curC))
                        if any(not any(v+lo<=a<=v+hi for a in (0,1)) for i,v in zip(curC,cv) for lo,hi in (bounds[i,k],)):continue
                    key=(cv,tuple(fval.get(i,0) for i in curF));old,rep=N.get(key,(0,w|(bit<<j)));N[key]=(trim(old+mass),rep)
                    observed_peak=max(observed_peak,len(N))
                    if len(N)>max_states:stop="state_cap";raise Refused()
            D=N;prevC,prevF=curC,curF;peak=max(peak,len(D));completed_layers=k+1
            if not D:return out('EMPTY',count=0)
        mass,w=D.get(((),()),(0,0));assert mass
        B.pay(1+n*(n+1)+len(H)*(n+1)+sum(1+len(c) for c in F+O));x=tuple(int(a+sum(v*(w>>k&1) for k,v in s.items())) for a,s in C)
        assert all(v in (0,1) for v in x) and all(sum(v*y for v,y in zip(r,x))==s for r,s in zip(A,b)) and all(any(x[abs(l)-1]==int(l>0) for l in c) for c in F) and all(sum(v*y for v,y in zip(r,x))%3==s%3 for r,s in zip(H,t)) and all(sum(x[i] for i in c)==1 for c in O)
        return out('WITNESS',count=mass,witness=x,free=len(J))
    except Refused:
        if stop is None:stop='logical_cap'
        return out('UNKNOWN')


def main():
    from itertools import product
    from random import Random
    from collections import Counter
    rng=Random(3693602);C=Counter()
    for n in range(9):
        for _ in range(24):
            A=tuple(tuple(rng.randrange(-2,3) for j in range(n)) for i in range(rng.randrange(4)));b=tuple(rng.randrange(-2,3) for r in A);F=tuple(tuple(rng.choice((-1,1))*rng.randrange(1,n+1) for j in range(3)) for i in range(rng.randrange(4))) if n else ();H=tuple(tuple(rng.randrange(3) for j in range(n)) for i in range(rng.randrange(2)));t=tuple(rng.randrange(3) for r in H);O=tuple(tuple(j for j in range(n) if rng.randrange(2)) for i in range(rng.randrange(2)))
            W=[x for x in product((0,1),repeat=n) if all(sum(a*v for a,v in zip(r,x))==s for r,s in zip(A,b)) and all(any(x[abs(l)-1]==int(l>0) for l in c) for c in F) and all(sum(a*v for a,v in zip(r,x))%3==s for r,s in zip(H,t)) and all(sum(x[j] for j in c)==1 for c in O)]
            p=list(range(n));rng.shuffle(p)
            for clip in (None,2):
                q=solve(A,b,n,F,H,t,O,10**7,clip,p);assert q['count']==(len(W) if clip is None else min(2,len(W)))
                if W:assert q['witness'] in W
                C[q['status']]+=1
    for n in (16,32,64,128):
        A=((1,)*n,);q=solve(A,(1,),n,cap=10**8);assert q['count']==n and q['peak']<=n
        z=solve(A,(n//2,),n,cap=10**8);from math import comb
        assert z['count']==comb(n,n//2);print('wide_affine',n,q['peak'],q['steps'],z['peak'],z['steps'])
    assert solve(((1,),),(1,),1,cap=0)['status']=='UNKNOWN'
    assert solve((),(),3,F=((1,2),(2,3)),max_states=1)['status']=='UNKNOWN'
    print(dict(C),'refusals PASS')
if __name__=='__main__':main()
