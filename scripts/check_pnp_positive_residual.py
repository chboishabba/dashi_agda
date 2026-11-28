"""Positive mass receiver on original residual; bounded local projection and free F3 lift.
Declared work, not a physical tape clock. None is refusal, not emptiness.
"""
from itertools import product
from check_pnp_conditional_autarky import project
from check_pnp_live_signed_orbit_join import Refused, accepts
from check_pnp_mobius_prefix import prefix_portfolio
from check_pnp_binary_support_endpoint import child_bounds

def project_lift(C,R,rows,t,n,B,width=4):
    B.pay(1+len(R)+sum(1+len(c) for c in C)+len(rows)*(n+1))
    if () in C:return None
    D=tuple(sorted({abs(l)-1 for c in C for l in c}))
    assert set(D)<=set(R)
    if D:
        P,spent=project(C,n,D,B.left,width,rows);B.pay(spent)
        if P is None:return None
        assert not P['S'] and not P['G']
        K={s:dict(zip(D,d)) for (boundary,s),(d,mass) in P['table'].items()}
    else:K={(0,)*len(rows):{}}
    for i in R:
        if i in D:continue
        B.pay(1+2*len(K)*(1+len(rows)+len(R)))
        H={s:w|{i:0} for s,w in K.items()}
        for s,w in K.items():
            u=tuple((v+r[i])%3 for v,r in zip(s,rows))
            H.setdefault(u,w|{i:1})
        K=H
    w=K.get(tuple(t))
    if w is None:return None
    B.pay(1+len(R)*(1+len(rows))+sum(1+len(c) for c in C))
    assert accepts(C,w) and tuple(sum(r[i]*w[i] for i in R)%3 for r in rows)==tuple(t)
    return w

def binary_lift(C,R,cols,t,lo,hi,B,data_clock=None):
    # Binary observation labels give contrast2=-mass; retain inherited
    # positive parent bounds, one certified child observation per bit.
    lower=(lo[0]+1)//2;upper=hi[0]//2;z={}
    for j,i in enumerate(R):
        reserve=B.left//(len(R)-j)
        if not reserve:return None
        B.pay(reserve)
        A=tuple(c[:-1]+(int(k==i),) for k,c in enumerate(cols))
        q=prefix_portfolio(C,A,t,0,R,1,work_cap=reserve,data_clock=data_clock)
        if q is None:return None
        L,U,_,_=child_bounds(q[0],q[1],lower,upper)
        if max(L)<=0:return None
        b=max(range(2),key=lambda b:(L[b],-b))
        C=C+(((i+1) if b else -(i+1),),);z[i]=b
        lower,upper=L[b],U[b]
    return z

def recover(C,R,rows,cols,t,n,lo,hi,B,data_clock=None):
    from check_pnp_live_signed_orbit_join import Budget
    # Reserve local projection separately. Failed work is never refunded.
    if not R:return {}
    try:B.pay(1+sum(1+len(c) for c in C))
    except Refused:return None
    if len({abs(l)-1 for c in C for l in c})<=4:
        cap=3*B.left//4;B.pay(cap);A=Budget(cap)
        try:
            z=project_lift(C,R,rows,t,n,A)
            if z is not None:return z
        except Refused:pass
    # Try a bounded original witness probe, not a second global count.
    cap=B.left//2;B.pay(cap);A=Budget(cap)
    try:
        for bits in product((0,1),repeat=len(R)):
            A.pay(1+len(R)*(1+len(rows))+sum(1+len(c) for c in C))
            z=dict(zip(R,bits))
            if accepts(C,z) and tuple(sum(r[i]*z[i] for i in R)%3 for r in rows)==tuple(t):return z
    except Refused:pass
    return binary_lift(C,R,cols,t,lo,hi,B,data_clock)
