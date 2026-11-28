"""Reverse context transport on a completed exact separator trace.
Clipped tables cannot be used for normalized contrasts; replay exact first.
"""
from itertools import product
from collections import defaultdict
from math import prod
from check_pnp_boolean_separator import source,evaluate,value,fold,replay,Reservation,Refused


def marginals(A,b,n,F,H,t,O,q,cap):
    B=Reservation(cap)
    if q['status']=='UNKNOWN':return dict(status='UNKNOWN',used=0)
    # Replay all table entries before using any retained count as exact.
    a=cap//2;B.pay(a)
    if not replay(A,b,n,F,H,t,O,q,a):return dict(status='UNKNOWN',used=cap-B.left)
    if q['status']=='EMPTY':return dict(status='EMPTY',mass=0,counts=((0,0),)*n,used=cap-B.left)
    try:
        (J,C,fs),_=source(A,b,n,F,H,t,O,B);active=set(range(len(fs)));scopes={i:f[0] for i,f in enumerate(fs)};T={};ctx={};counts=[[0,0] for _ in range(n)];points=0
        for k,(j,ids,S,V,W) in enumerate(q['trace']):
            B.pay(1+len(ids)+len(S));out=len(fs)+k;active.difference_update(ids);active.add(out);scopes[out]=S;T[out]=V;ctx[out]=defaultdict(int)
        def val(i,u):
            if i<len(fs):return evaluate(C,fs[i],u,B)
            B.pay(1+len(scopes[i]));return T[i].get(tuple(u[k] for k in scopes[i]),0)
        def distribute(ids,u,context):
            nonlocal points
            B.pay(1+len(ids));v=[val(i,u) for i in ids];points+=1
            if not context or not all(v):return 0
            # Positive global contribution; all retired child carriers
            # are disjoint given their boundaries. Divide out the exact
            # local mass to obtain the external context of that child.
            mass=context*prod(v)
            for i,m in zip(ids,v):
                B.pay(1+len(scopes[i]))
                if i>=len(fs):ctx[i][tuple(u[k] for k in scopes[i])]+=mass//m
                elif i<n:
                    z=value(C,i,u);assert z in (0,1);counts[i][int(z)]+=mass
            return mass
        assert distribute(tuple(sorted(active)),{},1)==q['count']
        for k in reversed(range(len(q['trace']))):
            j,ids,S,V,W=q['trace'][k];out=len(fs)+k
            # Only boundary values with a nonzero outside context can
            # contribute to a global satisfying assignment.
            for s,c in ctx[out].items():
                B.pay(1+len(S));assert s in V;u=dict(zip(S,s));total=0
                for v in (0,1):u[j]=v;total+=distribute(ids,u,c)
                assert total==c*V[s]
        assert all(a+b==q['count'] for a,b in counts)
        return dict(status='COMPLETE',mass=q['count'],counts=tuple(map(tuple,counts)),points=points,used=cap-B.left)
    except Refused:return dict(status='UNKNOWN',used=cap-B.left)


def main():
    from random import Random
    from check_pnp_boolean_separator import audit
    rng=Random(3693503);cases=coordinates=0
    for n in range(9):
        for _ in range(24):
            A=tuple(tuple(rng.randrange(-1,2) for j in range(n)) for i in range(rng.randrange(3)));b=tuple(rng.randrange(-1,2) for i in A)
            F=tuple(tuple(rng.choice((-1,1))*rng.randrange(1,n+1) for j in range(2)) for i in range(rng.randrange(4))) if n else ()
            H=tuple(tuple(rng.randrange(3) for j in range(n)) for i in range(rng.randrange(2)));t=tuple(rng.randrange(3) for r in H);O=()
            W=[x for x in product((0,1),repeat=n) if audit(A,b,n,F,H,t,O,x,Reservation(10**7))]
            q=fold(A,b,n,F,H,t,O,cap=10**7);z=marginals(A,b,n,F,H,t,O,q,10**7)
            assert z['mass']==len(W) and z['counts']==tuple((sum(x[i]==0 for x in W),sum(x[i]==1 for x in W)) for i in range(n));cases+=1;coordinates+=n
    for k in (16,32,64,128):
        F=tuple((1,i) for i in range(2,k+1));q=fold((),(),k,F,cap=10**7);z=marginals((),(),k,F,(),(),(),q,10**8)
        assert z['counts']==((1,2**(k-1)),)+((2**(k-2),1+2**(k-2)),)*(k-1)
        print('star marginals',k,z['points'],z['used'])
    q=fold((),(),4,F=((1,2),),clip=2);assert marginals((),(),4,((1,2),),(),(),(),q,10**6)['status']=='UNKNOWN'
    q=fold((),(),4);assert marginals((),(),4,(),(),(),(),q,0)['status']=='UNKNOWN'
    print('marginals',cases,'coordinates',coordinates,'clipped/refusal PASS')
if __name__=='__main__':main()
