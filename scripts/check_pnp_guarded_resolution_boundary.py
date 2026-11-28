"""Restrict actual resolution DAGs and recover original guard payload.
A separate original incidence capacity certificate bypasses PHP resolution.
"""
from check_pnp_frontier_resolution import norm,resolvent,replay,learn,accepts
from check_pnp_source_derived_cover import Reservation,Refused


def restrict_clause(c,pin):
    if any(pin.get(abs(l)-1)==int(l>0) for l in c):return None
    return tuple(l for l in norm(c) if abs(l)-1 not in pin)


def restrict_proof(F,n,proof,pin,cap):
    B=Reservation(cap);D=replay(F,n,proof,B)
    if D is None:raise ValueError('invalid receipt')
    if any(not 0<=i<n or b not in (0,1) for i,b in pin.items()):raise ValueError('pin')
    R=[];refs=[];steps=[]
    for c in D[:len(F)]:
        B.pay(1+len(c));r=restrict_clause(c,pin)
        refs.append(None if r is None else len(R))
        if r is not None:R.append(r)
    base=tuple(R)
    for k,(i,j,p,c) in enumerate(proof):
        B.pay(1+len(c)+len(D[i])+len(D[j]));r=restrict_clause(c,pin)
        if r is None:refs.append(None);continue
        a,b=refs[i],refs[j];v=abs(p)-1
        if v in pin:z=a if pin[v]!=int(p>0) else b
        else:
            assert a is not None and b is not None
            if p not in R[a]:z=a
            elif -p not in R[b]:z=b
            else:
                u=resolvent(R[a],R[b],p);B.pay(1+len(u));z=len(R);R.append(u);steps.append((a,b,p,u))
        assert z is not None and set(R[z])<=set(r);refs.append(z)
    assert replay(base,n,steps,B)==tuple(R)
    assert len(steps)<=len(proof)
    return base,tuple(steps),tuple(refs),tuple(R)


def guarded(F,n):
    # selector coordinate n (literal n+1); exact all-zero anchor
    s=n+1;H=tuple((s,-(i+1)) for i in range(n))+tuple((-s,)+c for c in F)
    return H,H+(tuple(range(1,n+2)),)


def php(p,h):
    rows=tuple(tuple(i*h+j+1 for j in range(h)) for i in range(p))
    cols=tuple(tuple(i*h+j+1 for i in range(p)) for j in range(h))
    F=rows+tuple((-a,-b) for c in cols for i,a in enumerate(c) for b in c[i+1:])
    return F,p*h


def capacity(F,n,cap):
    """Recognize disjoint positive row cover and negative clique partition.
    Actual original clauses suffice for a cardinality contradiction.
    No promise that source is PHP; failed recognition is UNKNOWN.
    """
    B=Reservation(cap)
    try:
        B.pay(1+n+sum(1+len(c) for c in F));P=tuple(c for c in map(norm,F) if c and min(c)>0)
        if sorted(l for c in P for l in c)!=list(range(1,n+1)):return dict(status='UNKNOWN')
        E=[set() for _ in range(n+1)]
        for c in map(norm,F):
            if len(c)==2 and max(c)<0:
                a,b=map(abs,c);E[a].add(b);E[b].add(a)
        U=set(range(1,n+1));Q=[]
        while U:
            B.pay(1);a=min(U);todo=[a];U.remove(a);C=[]
            while todo:
                v=todo.pop();C.append(v);B.pay(1+len(E[v]));new=E[v]&U;U-=new;todo.extend(new)
            if any(len(E[v])!=len(C)-1 for v in C):return dict(status='UNKNOWN')
            Q.append(tuple(sorted(C)))
        if len(P)<=len(Q):return dict(status='UNKNOWN')
        return dict(status='EMPTY',rows=P,columns=tuple(Q),used=cap-B.left)
    except Refused:return dict(status='UNKNOWN')


def main():
    from itertools import product
    from random import Random
    rng=Random(3693104);checks=steps=0
    for n in range(1,7):
        for _ in range(32):
            F=tuple(tuple(rng.choice((-1,1))*rng.randrange(1,n+1) for _ in range(rng.randrange(1,4))) for _ in range(4*n))
            if any(accepts(F,x) for x in product((0,1),repeat=n)):continue
            H,G=guarded(F,n);q=learn(G,n+1,10**7);assert q['status']=='EMPTY'
            base,ps,refs,D=restrict_proof(G,n+1,q['proof'],{n:1},10**7)
            assert base==tuple(map(norm,F)) and D[refs[q['empty_id']]]==();checks+=1;steps+=len(ps)
    for h in (1,2,3):
        F,n=php(h+1,h);H,G=guarded(F,n);q=learn(G,n+1,10**7);assert q['status']=='EMPTY'
        base,ps,refs,D=restrict_proof(G,n+1,q['proof'],{n:1},10**7);assert base==tuple(map(norm,F)) and D[refs[q['empty_id']]]==();checks+=1;steps+=len(ps)
        print('php restriction',h,len(q['proof']),len(ps))
    for h in (4,8,16,32,64):
        F,n=php(h+1,h);H,G=guarded(F,n)
        # Actual guard branch restriction, not external row labels.
        R=tuple(r for c in G if (r:=restrict_clause(c,{n:1})) is not None)
        q=capacity(R,n,10**7);assert q['status']=='EMPTY' and len(q['rows'])==h+1 and len(q['columns'])==h
        print('php capacity',h,n,q['used'])
    F,n=php(4,4);assert capacity(F,n,10**7)['status']=='UNKNOWN'
    F,n=php(5,4);assert capacity(F[:-1],n,10**7)['status']=='UNKNOWN';assert capacity(F,n,0)['status']=='UNKNOWN'
    print(dict(guarded_restrictions=checks,restricted_proof_steps=steps,capacity_controls=5,negative_controls=3))
if __name__=='__main__':main()
