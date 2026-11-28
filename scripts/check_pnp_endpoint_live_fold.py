"""Original constraint boundary fold: clause, F3 and exact-one rows.
Retire a constraint only at its last original coordinate. Keep exact or
clipped occupancy and original representatives. Scoped logical allowance.
"""
from check_pnp_source_derived_cover import Reservation, Refused
from check_pnp_bit_data_schedule import Refused as DataRefused, add, code, value
from check_pnp_nat_bit_schedule import NatOps


def solve(F,n,rows,target,one,cap,clip=None,order=None,data_clock=None):
    B=Reservation(cap);D={(): (1,0)};peak=1;width=0;done=0
    if n<0 or len(rows)!=len(target) or any(len(r)!=n for r in rows) or clip not in (None,2):raise ValueError('source')
    try:
        B.pay(1+n+sum(1+len(c) for c in F)+len(rows)*(n+1)+sum(1+len(c) for c in one))
        order=tuple(range(n)) if order is None else tuple(order)
        if len(order)!=n or set(order)!=set(range(n)):raise ValueError('order')
        pos={v:i for i,v in enumerate(order)}; factors=[]
        def factor(kind,terms,t):
            if not terms:return t==0
            first=min(pos[v] for v in terms);last=max(pos[v] for v in terms)
            factors.append((kind,terms,t,first,last));return True
        for c in F:
            terms={}
            for l in c:
                if not 1<=abs(l)<=n:raise ValueError('literal')
                terms[abs(l)-1]=terms.get(abs(l)-1,0)|(1<<int(l>0))
            if not factor('or',terms,1):return dict(status='EMPTY',count=0,witness=None,reserved=cap-B.left,peak=peak,width=width)
        for a,t in zip(rows,target):
            if not factor('f3',{i:b%3 for i,b in enumerate(a) if b%3},t%3):return dict(status='EMPTY',count=0,witness=None,reserved=cap-B.left,peak=peak,width=width)
        for c in one:
            if len(set(c))!=len(c) or any(not 0<=i<n for i in c):raise ValueError('incidence')
            if not factor('one',{i:1 for i in c},1):return dict(status='EMPTY',count=0,witness=None,reserved=cap-B.left,peak=peak,width=width)
        ops=None if data_clock is None else NatOps(data_clock)
        prev=()
        for j,i in enumerate(order):
            B.pay(1+len(factors))
            active=tuple(k for k,f in enumerate(factors) if f[3]<=j<=f[4]);keep=tuple(k for k in active if factors[k][4]>j)
            width=max(width,len(active));before={k:p for p,k in enumerate(prev)};N={}
            B.pay(1+2*len(D)*(3+len(active)+len(keep)+(n+7)//8))
            for key,(mass,w) in D.items():
                for b in (0,1):
                    vals=[];ok=True
                    for k in active:
                        kind,terms,t,first,last=factors[k];u=key[before[k]] if k in before else 0;c=terms.get(i,0)
                        if kind=='or':z=int(bool(u or (c>>b&1))) if ops is None else data_clock.OR(u,c>>b&1)
                        elif kind=='f3':z=(u+b*c)%3 if ops is None else value(add(data_clock,code(u),code(b*c)))
                        else:
                            z=u+b*c if ops is None else ops.add(u,b*c)
                            if z>1:ok=False;break
                        if j==last:
                            if z!=t:ok=False;break
                        else:vals.append(z)
                    if not ok:continue
                    v=tuple(vals);old,rep=N.get(v,(0,w|(b<<i)));total=old+mass if ops is None else ops.add(old,mass)
                    N[v]=(min(2,total) if clip==2 else total,rep)
            D=N;prev=keep;done=j+1;peak=max(peak,len(D))
            if not D:break
        count,w=D.get((),(0,0));assert not D or done==n
        x=tuple((w>>i)&1 for i in range(n)) if count else None
        if x is not None:
            B.pay(1+n+sum(1+len(c) for c in F)+len(rows)*(n+1)+sum(1+len(c) for c in one))
            assert all(any(x[abs(l)-1]==int(l>0) for l in c) for c in F)
            assert tuple(sum(a*b for a,b in zip(r,x))%3 for r in rows)==tuple(t%3 for t in target)
            assert all(sum(x[i] for i in c)==1 for c in one)
        return dict(status='WITNESS' if count else 'EMPTY',count=count,witness=x,reserved=cap-B.left,peak=peak,width=width,clipped=clip==2)
    except (Refused,DataRefused):return dict(status='UNKNOWN',reserved=cap-B.left,peak=peak,width=width,completed=done)


def guarded(F,n,cap):
    # selector is original coordinate zero; anchor all other bits zero.
    G=tuple((1,-(i+2)) for i in range(n))+tuple((-1,)+tuple((abs(l)+1)*(1 if l>0 else -1) for l in c) for c in F)
    q=solve(G,n+1,(),(),(),cap,clip=2)
    if q['status']=='UNKNOWN':return dict(q,decision='UNKNOWN')
    assert q['count'] in (1,2)
    return dict(q,decision='UNSAT' if q['count']==1 else 'SAT')


def main():
    from itertools import product
    from random import Random
    from collections import Counter
    from check_pnp_bit_data_schedule import Clock
    rng=Random(3692901);C=Counter();data=Clock(10**8)
    for n in range(9):
        for _ in range(40):
            F=tuple(tuple(rng.choice((-1,1))*rng.randrange(1,n+1) for _ in range(rng.randrange(4))) for _ in range(rng.randrange(5))) if n else ()
            A=tuple(tuple(rng.randrange(3) for _ in range(n)) for _ in range(rng.randrange(4)));t=tuple(rng.randrange(3) for _ in A)
            O=tuple(tuple(sorted(rng.sample(range(n),rng.randrange(min(n,4)+1)))) for _ in range(rng.randrange(4)))
            W=[x for x in product((0,1),repeat=n) if all(any(x[abs(l)-1]==int(l>0) for l in c) for c in F) and tuple(sum(a*b for a,b in zip(r,x))%3 for r in A)==t and all(sum(x[i] for i in c)==1 for c in O)]
            for clip in (None,2):
                order=list(range(n));rng.shuffle(order);q=solve(F,n,A,t,O,10**7,clip,order,data)
                assert q['count']==(len(W) if clip is None else min(2,len(W)))
                if W:assert q['witness'] in W
                C['mixed']+=1
            q=guarded(F,n,10**7);assert q['decision']==('SAT' if any(all(any(x[abs(l)-1]==int(l>0) for l in c) for c in F) for x in product((0,1),repeat=n)) else 'UNSAT');C['guarded']+=1
    # Original X3C: every selected column covers exactly three rows.
    for n in (4,8,16,32,64,128):
        # cycle of paired columns: each vertex pair is repeated on three distinct elements.
        O=tuple((i,(i+1)%n) for i in range(n) for _ in range(1)) + tuple((i,i+1) for i in range(0,n,2))
        assert all(sum(i in c for c in O)==3 for i in range(n))
        q=solve((),n,(),(),O,10**7);assert q['count']==2 and q['peak']<=4;C['x3c']+=1
        q=solve(((1,),),n,(),(),O,10**7,clip=2);assert q['count']==1;C['singleton']+=1
        q=solve(((1,),(2,)),n,(),(),O,10**7);assert q['count']==0;C['empty']+=1
    # Nontrivial connected dense mixed source must be allowed to refuse.
    n=24;O=tuple((i,j) for i in range(n) for j in range(i+1,n));q=solve((),n,(),(),O,64);assert q['status']=='UNKNOWN';C['refusal']+=1
    print(dict(C),data.cap-data.left)
if __name__=='__main__':main()
