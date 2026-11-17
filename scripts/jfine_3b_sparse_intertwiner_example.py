#!/usr/bin/env python3
"""Exact weight-projector intertwiner recovery in a toy F7 Heisenberg module.
An ACTUAL Monster matrix input is not supplied; this checks the algorithm,
including its fail-closed response to inconsistent target generators.
"""
from itertools import product
import json
P,R=7,2
def eye(n):return [[int(i==j) for j in range(n)] for i in range(n)]
def add(A,B):return [[(a+b)%P for a,b in zip(x,y)] for x,y in zip(A,B)]
def scale(k,A):return [[k*x%P for x in row] for row in A]
def mm(A,B):return [[sum(x*y for x,y in zip(row,col))%P for col in zip(*B)] for row in A]
def col(A,k):return [row[k] for row in A]
def cols(v):return [list(row) for row in zip(*v)]
def rref(A, inverse=False):
    n=len(A); width=len(A[0]); B=[a[:]+e[:] for a,e in zip(A,eye(n))] if inverse else [a[:] for a in A]
    piv=0
    for j in range(width):
        k=next((i for i in range(piv,n) if B[i][j]),None)
        if k is None:continue
        B[piv],B[k]=B[k],B[piv]
        t=pow(B[piv][j],-1,P); B[piv]=[(x*t)%P for x in B[piv]]
        for i in range(n):
            if i!=piv:
                t=B[i][j]; B[i]=[(x-t*y)%P for x,y in zip(B[i],B[piv])]
        piv+=1
        if piv==n:break
    if inverse:
        if piv<n:raise ValueError("singular")
        return [r[width:] for r in B]
    return piv
def A0(n,m,i):
    X=list(product(range(3),repeat=n)); d=len(X)*m; out=[[0]*d for _ in range(d)]
    for j,u in enumerate(X):
        v=tuple((a+int(k==i))%3 for k,a in enumerate(u))
        for q in range(m):out[X.index(v)*m+q][j*m+q]=1
    return out
def B0(n,m,i):
    X=list(product(range(3),repeat=n));d=len(X)*m;out=[[0]*d for _ in range(d)]
    for j,u in enumerate(X):
        for q in range(m):out[j*m+q][j*m+q]=pow(R,u[i],P)
    return out
def reconstruct(n,m,A,B):
    d=m*3**n;I=eye(d);proj=I
    for b in B:
        proj=mm(proj,scale(pow(3,-1,P),add(add(I,b),mm(b,b))))
    assert mm(proj,proj)==proj
    base=[]
    for j in range(d):
        v=col(proj,j)
        if rref(cols(base+[v]))>len(base):base.append(v)
        if len(base)==m:break
    assert len(base)==m
    out=[]
    for u in product(range(3),repeat=n):
        v=base[:]
        for i,a in enumerate(u):
            for _ in range(a):v=[col(mm(A[i],cols([w])),0) for w in v]
        out.extend(v)
    T=cols(out)
    assert rref(T)==d
    for i in range(n):
        assert mm(A[i],T)==mm(T,A0(n,m,i))
        assert mm(B[i],T)==mm(T,B0(n,m,i))
    return T,proj
def audit():
    n,m=2,2;d=m*3**n
    S=eye(d)
    for i in range(d-1):
        for j in range(d):S[i][j]=(S[i][j]+2*S[i+1][j])%P
    Si=rref(S,inverse=True)
    twist=lambda x:mm(mm(S,x),Si)
    A=[twist(A0(n,m,i)) for i in range(n)]
    B=[twist(B0(n,m,i)) for i in range(n)]
    T,proj=reconstruct(n,m,A,B)
    damaged=B[:];damaged[0]=add(damaged[0],eye(d))
    caught=False
    try:reconstruct(n,m,A,damaged)
    except (AssertionError,ValueError):caught=True
    assert caught
    return dict(field="F7",cube_root=R,dimension=d,intertwiner_rank=rref(T),
                projector_rank=rref(proj),corrupted_generator_rejected=caught,
                actual_monster_generators_supplied=False)
if __name__=="__main__":print(json.dumps(audit(),indent=2))
