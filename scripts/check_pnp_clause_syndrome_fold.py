"""Actual residual clause satisfaction mask x affine syndrome, with original lifts.
Logical allowance only; no uniform polynomial bound on reachable masks.
"""
from check_pnp_source_derived_cover import Reservation,Refused
from check_pnp_affine_pin_dispatch import solve_pins
from check_pnp_bit_data_schedule import audit,Refused as DataRefused

def fold(F,n,rows,target,B,data_clock=None):
    if n<0 or len(rows)!=len(target) or any(len(r)!=n for r in rows) or any(not 1<=abs(l)<=n for c in F for l in c):raise ValueError('source')
    m=len(F);r=len(rows);B.pay(1+n*(r+1)+sum(1+len(c) for c in F))
    masks=[[0,0] for _ in range(n)];last=[0]*n
    for j,c in enumerate(F):
        if not c:return dict(status='EMPTY',count=0)
        for l in c:masks[abs(l)-1][int(l>0)]|=1<<j
        last[max(abs(l)-1 for l in c)]|=1<<j
    from check_pnp_nat_bit_schedule import NatOps
    from check_pnp_bit_data_schedule import add,code,value
    ops=None if data_clock is None else NatOps(data_clock)
    D={(0,(0,)*r):(1,0)};required=0;peak=1
    for i in range(n):
        required|=last[i];B.pay(1+2*len(D)*(2+r+(m+n+7)//8));N={}
        for (mask,s),(mass,w) in D.items():
            for b in (0,1):
                z=mask|masks[i][b]
                if z&required!=required:continue
                key=(z,tuple((u+b*a[i])%3 if ops is None else value(add(data_clock,code(u),code((b*a[i])%3))) for u,a in zip(s,rows)))
                old,rep=N.get(key,(0,w|(b<<i)));N[key]=(old+mass if ops is None else ops.add(old,mass),rep)
        D=N;peak=max(peak,len(D))
    count,w=D.get(((1<<m)-1,tuple(t%3 for t in target)),(0,0))
    return dict(status='WITNESS' if count else 'EMPTY',count=count,witness=tuple((w>>i)&1 for i in range(n)) if count else None,peak=peak)

def solve_fold(F,n,rows,target,cap,data_clock=None):
    # Reserve only when the conservative number of reachable keys fits.
    m=len(F);r=len(rows)
    base=1+n*(r+1)+sum(1+len(c) for c in F)
    upper=base+n+sum(2*min(1<<i,(1<<m)*3**r)*(2+r+(m+n+7)//8) for i in range(n))
    # Bound by both original prefixes and possible mask/syndrome keys.
    if upper<=cap:
        B=Reservation(cap)
        try:q=fold(F,n,rows,target,B,data_clock)
        except DataRefused:return dict(status='UNKNOWN',reserved=cap-B.left,route='clause_syndrome',stop='fold_data_clock')
        q['reserved']=cap-B.left
        if q['status']=='WITNESS':
            x=q['witness'];assert all(any(x[abs(l)-1]==int(l>0) for l in c) for c in F)
            assert tuple(sum(a*b for a,b in zip(row,x))%3 for row in rows)==tuple(t%3 for t in target)
            if data_clock is not None:
                try:assert audit(F,tuple(tuple(a%3 for a in row) for row in rows),tuple(t%3 for t in target),x,data_clock)
                except DataRefused:q['status']='WITNESS_DATA_AUDIT_REFUSED'
        return dict(q,route='clause_syndrome')
    return dict(solve_pins(F,n,rows,target,cap,data_clock=data_clock),route='pins')

def main():
    from itertools import product
    from random import Random
    from collections import Counter
    from check_pnp_bit_data_schedule import Clock
    C=Counter();rng=Random(36943);data=Clock(10**8)
    for n in range(9):
        for k in range(16):
            F=tuple(tuple((i+1)*rng.choice((-1,1)) for i in rng.sample(range(n),rng.randrange(min(n,4)+1))) for _ in range(k%7))
            A=(tuple(rng.randrange(3) for i in range(n)),)
            for t in range(3):
                old=solve_pins(F,n,A,(t,),4096)
                for cap in (0,4096,10**7):
                    q=solve_fold(F,n,A,(t,),cap,data_clock=data)
                    W=[x for x in product((0,1),repeat=n) if all(any(x[abs(l)-1]==int(l>0) for l in c) for c in F) and sum(a*b for a,b in zip(A[0],x))%3==t]
                    assert q['reserved']<=cap
                    if q['status']=='WITNESS':assert q['witness'] in W
                    if q['status']=='EMPTY':assert not W
                    if 'count' in q:assert q['count']==len(W)
                    if cap:assert q['status']==('WITNESS' if W else 'EMPTY')
                    if cap==4096:C[old['status'],q['status']]+=1
    print('baseline',dict(C),'charged',data.cap-data.left)
    # Independently seeded multi-row, duplicate and tautological clauses.
    rng=Random(271828);tests=0
    for n in range(1,10):
        for _ in range(32):
            F=tuple(tuple(rng.choice((-1,1))*rng.randrange(1,n+1) for _ in range(rng.randrange(5))) for _ in range(rng.randrange(7)))
            A=tuple(tuple(rng.randrange(3) for _ in range(n)) for _ in range(rng.randrange(4)))
            t=tuple(rng.randrange(3) for _ in A)
            q=fold(F,n,A,t,Reservation(10**7))
            W=[x for x in product((0,1),repeat=n) if all(any(x[abs(l)-1]==int(l>0) for l in c) for c in F) and tuple(sum(a*b for a,b in zip(row,x))%3 for row in A)==t]
            assert q['count']==len(W)
            if W:assert q['witness'] in W
            tests+=1
    q=solve_fold(((1,),),1,(),(),4096,data_clock=Clock(0));assert q['status']=='UNKNOWN'
    print('independent exact',tests,'data refusal PASS')
if __name__=='__main__':main()
