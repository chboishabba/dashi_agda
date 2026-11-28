"""Exact elementary F3 row receipts and original-equation coefficients.
Replay checks both directions using invertible operations, not just row span.
"""
from check_pnp_f3_syndrome_boundary import rref
from check_pnp_source_derived_cover import Reservation,Refused

def apply(A,op):
    kind,i,j,k=op
    if not 0<=i<len(A) or not 0<=j<len(A):raise ValueError('index')
    if kind=='swap' and k==0:A[i],A[j]=A[j],A[i]
    elif kind=='scale' and i==j and k in (1,2):A[i]=[(k*x)%3 for x in A[i]]
    elif kind=='add' and i!=j and k in (1,2):A[i]=[(x+k*y)%3 for x,y in zip(A[i],A[j])]
    else:raise ValueError('operation')

def inverse(op):
    kind,i,j,k=op
    return (kind,i,j,(-k)%3) if kind=='add' else op

def produce(rows,n,B):
    m=len(rows);B.pay(1+m*(n+1+m));A=[list(row) for row in rows]
    if any(len(a)!=n+1 or any(v not in (0,1,2) for v in a) for a in A):raise ValueError('matrix')
    U=[[int(i==j) for j in range(m)] for i in range(m)];ops=[];p=0;piv=[]
    def emit(op):
        B.pay(1+n+1+m);apply(A,op);apply(U,op);ops.append(op)
    for j in range(n):
        B.pay(1+m-p);i=next((i for i in range(p,m) if A[i][j]),None)
        if i is None:continue
        if i!=p:emit(('swap',p,i,0))
        emit(('scale',p,p,A[p][j]))
        for i in range(m):
            B.pay(1)
            if i!=p and A[i][j]:emit(('add',i,p,-A[i][j]%3))
        piv.append(j);p+=1
    return dict(rows=tuple(map(tuple,A)),coeff=tuple(map(tuple,U)),piv=tuple(piv),ops=tuple(ops))

def verify(rows,n,receipt,B):
    m=len(rows);B.pay(1+m*(n+1+m));A=[list(a) for a in rows];U=[[int(i==j) for j in range(m)] for i in range(m)]
    for op in receipt['ops']:
        B.pay(1+n+1+m);apply(A,op);apply(U,op)
    if tuple(map(tuple,A))!=receipt['rows'] or tuple(map(tuple,U))!=receipt['coeff']:return False
    B.pay(1+m*m*(n+1))
    if any(a[j]!=sum(c[k]*rows[k][j] for k in range(m))%3 for a,c in zip(A,U) for j in range(n+1)):return False
    p=len(receipt['piv']);P=receipt['piv']
    if any(not 0<=j<n for j in P) or tuple(sorted(set(P)))!=P or p>m:return False
    if any(A[i][j]!=int(i==k) for k,j in enumerate(P) for i in range(m)):return False
    if any(any(A[i][:P[i]]) for i in range(p)) or any(any(a[:n]) for a in A[p:]):return False
    for op in reversed(receipt['ops']):
        B.pay(1+n+1);apply(A,inverse(op))
    return tuple(map(tuple,A))==tuple(map(tuple,rows))

def certified(rows,n,B):
    q=produce(rows,n,B)
    assert verify(rows,n,q,B)
    p=len(q['piv']);A=q['rows'];bad=next((i for i in range(p,len(A)) if A[i][-1]),None)
    return (None if bad is not None else (A[:p],q['piv'])),q

def main():
    from itertools import product
    from random import Random
    rng=Random(36927);checks=ops=0
    for n,m in product(range(7),range(7)):
        for _ in range(16):
            rows=tuple(tuple(rng.randrange(3) for j in range(n+1)) for i in range(m))
            rr,q=certified(rows,n,Reservation(10**7));assert rr==rref(rows,n)
            ops+=len(q['ops']);checks+=1
    rows=((1,1,0),(1,2,1));rr,q=certified(rows,2,Reservation(10000));bad=dict(q,coeff=((0,0),)+q['coeff'][1:]);assert not verify(rows,2,bad,Reservation(10000))
    try:certified(rows,2,Reservation(0));raise AssertionError('free certificate')
    except Refused:pass
    print(dict(matrices=checks,operations=ops,tamper_refusal=1,budget_refusal=1))
if __name__=='__main__':main()
