"""Exact original Boolean/F3 pin propagation before source cover.
Each forced pin has a unit-clause or singleton RREF row witness.
Logical reservation is separate from optional metered arithmetic.
"""
from check_pnp_f3_syndrome_boundary import rref
from check_pnp_source_derived_cover import Reservation, Refused, source_solve
from check_pnp_bit_data_schedule import rref_bits, audit, Refused as DataRefused


def reduce_source(F,n,rows,target,B,data_clock=None):
    if n<0 or len(rows)!=len(target) or any(len(a)!=n for a in rows) or any(not 1<=abs(l)<=n for c in F for l in c):raise ValueError('source')
    C=tuple(tuple(sorted(set(c))) for c in F);A=tuple(tuple(a%3 for a in r) for r in rows);t=tuple(b%3 for b in target)
    R=tuple(range(n));pins={};trace=[]
    while True:
        k=len(R);m=len(A)
        B.pay(1+k+sum(1+len(c) for c in C)+(m+1)*(k+1)*(1+m*k))
        rr=rref(tuple(a+(b,) for a,b in zip(A,t)),k) if data_clock is None else rref_bits(tuple(a+(b,) for a,b in zip(A,t)),k,data_clock)
        if rr is None or () in C:return dict(status='EMPTY',trace=trace)
        eq,piv=rr;forced={};why=[]
        def put(i,b,reason):
            if b not in (0,1) or (i in forced and forced[i]!=b):return False
            forced[i]=b;why.append((R[i],b,reason));return True
        for a in eq:
            S=tuple(i for i,b in enumerate(a[:-1]) if b)
            if len(S)==1:
                i=S[0]
                if not put(i,a[-1],('rref',a)):return dict(status='EMPTY',trace=trace,conflict=a)
        for c in C:
            if len(c)==1 and not put(abs(c[0])-1,int(c[0]>0),('unit',c)):
                return dict(status='EMPTY',trace=trace,conflict=c)
        if not forced:return dict(status='RESIDUAL',F=C,R=R,rows=tuple(a[:-1] for a in eq),target=tuple(a[-1] for a in eq),pins=pins,trace=trace)
        keep=tuple(i for i in range(k) if i not in forced);ix={i:j for j,i in enumerate(keep)};N=[]
        for c in C:
            if any(forced.get(abs(l)-1,-1)==int(l>0) for l in c):continue
            N.append(tuple((ix[abs(l)-1]+1)*(1 if l>0 else -1) for l in c if abs(l)-1 not in forced))
        pins.update((R[i],b) for i,b in forced.items());trace.append(tuple(why))
        t=tuple((a[-1]-sum(a[i]*b for i,b in forced.items()))%3 for a in eq)
        A=tuple(tuple(a[i] for i in keep) for a in eq);C=tuple(N);R=tuple(R[i] for i in keep)


def solve_pins(F,n,rows,target,cap,data_clock=None,**kw):
    B=Reservation(cap);reserve=cap//16;B.pay(reserve)
    try:q=reduce_source(F,n,rows,target,Reservation(reserve),data_clock)
    except (Refused,DataRefused):q=None
    if q is None:
        v=source_solve(F,n,rows,target,B.left,data_clock=data_clock,**kw)
        return dict(v,reserved=reserve+v['reserved'],pin_refused=True)
    if q['status']=='EMPTY':return dict(status='EMPTY',count=0,reserved=reserve,pin_trace=q['trace'])
    R=q['R'];P=q['pins']
    v=source_solve(q['F'],len(R),q['rows'],q['target'],B.left,data_clock=data_clock,**kw) if R else dict(status='WITNESS',witness=(),count=1,reserved=0)
    if v.get('witness') is not None:
        z=P|dict(zip(R,v['witness']));x=tuple(z[i] for i in range(n))
        assert all(any(x[abs(l)-1]==int(l>0) for l in c) for c in F)
        assert tuple(sum(a*b for a,b in zip(r,x))%3 for r in rows)==tuple(t%3 for t in target)
        v=dict(v,witness=x)
        if data_clock is not None:
            try:assert audit(F,tuple(tuple(a%3 for a in r) for r in rows),tuple(t%3 for t in target),x,data_clock)
            except DataRefused:v=dict(v,status='WITNESS_DATA_AUDIT_REFUSED')
    return dict(v,reserved=reserve+v['reserved'],pin_trace=q['trace'],pinned=len(P),remaining=len(R))


def main():
    from itertools import product
    from collections import Counter
    from random import Random
    rng=Random(36943);C=Counter();comparisons=0
    for n in range(9):
        for k in range(16):
            F=tuple(tuple((i+1)*rng.choice((-1,1)) for i in rng.sample(range(n),rng.randrange(min(n,4)+1))) for _ in range(k%7))
            rows=(tuple(rng.randrange(3) for i in range(n)),)
            for t in range(3):
                W=[x for x in product((0,1),repeat=n) if all(any(x[abs(l)-1]==int(l>0) for l in c) for c in F) and sum(a*b for a,b in zip(rows[0],x))%3==t]
                old=source_solve(F,n,rows,(t,),4096)
                for cap in (0,4096,10**7):
                    q=solve_pins(F,n,rows,(t,),cap);s=q['status'];assert q['reserved']<=cap
                    if s=='WITNESS':assert q['witness'] in W
                    if s=='EMPTY':assert not W
                    if s=='POSITIVE_NO_LIFT':assert W
                    if 'count' in q:assert q['count']==len(W)
                    if cap==10**7:assert s==('WITNESS' if W else 'EMPTY')
                    if cap==4096:C[old['status'],s]+=1
                    comparisons+=1
    n=6;F=tuple((i+1,j+1) for i in range(n) for j in range(i+1,n));A=tuple(tuple(int(i==j) for i in range(n)) for j in range(n))
    for t in ((1,)*n,(0,)*n,(2,)*n):
        q=solve_pins(F,n,A,t,100000);assert q['status']==('WITNESS' if t==(1,)*n else 'EMPTY')
    print(dict(comparisons=comparisons,transitions=dict(C),identity_controls=3))
if __name__=='__main__':main()
