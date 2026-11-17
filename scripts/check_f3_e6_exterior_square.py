#!/usr/bin/env python3
"""Exact finite verification for the F3^4 symplectic exterior-square / E6 bridge.

DASHI computation receipt only. This does not substitute for Agda/Lean kernel proofs.
"""
from __future__ import annotations
from collections import deque
from itertools import combinations, product
import numpy as np

MOD = 3

def tmat(A): return tuple(int(x) % MOD for x in np.array(A, dtype=int).reshape(-1))
def eye_t(n): return tmat(np.eye(n, dtype=int))
def mm_t(a, b, n):
    A = np.array(a, dtype=int).reshape(n, n)
    B = np.array(b, dtype=int).reshape(n, n)
    return tmat((A @ B) % MOD)

def rank_mod(A):
    A = np.array(A, dtype=int) % MOD
    r = 0
    for c in range(A.shape[1]):
        p = next((i for i in range(r, A.shape[0]) if A[i, c]), None)
        if p is None: continue
        A[[r, p]] = A[[p, r]]
        if A[r, c] == 2: A[r] = (2 * A[r]) % MOD
        for i in range(A.shape[0]):
            if i != r and A[i, c]: A[i] = (A[i] - A[i, c] * A[r]) % MOD
        r += 1
    return r

def inv_mod(A):
    A = np.array(A, dtype=int) % MOD
    n = A.shape[0]
    aug = np.concatenate([A, np.eye(n, dtype=int)], axis=1) % MOD
    row = 0
    for col in range(n):
        p = next((r for r in range(row, n) if aug[r, col]), None)
        if p is None: raise ValueError("singular")
        aug[[row, p]] = aug[[p, row]]
        if aug[row, col] == 2: aug[row] = (2 * aug[row]) % MOD
        for r in range(n):
            if r != row and aug[r, col]: aug[r] = (aug[r] - aug[r, col] * aug[row]) % MOD
        row += 1
    return aug[:, n:] % MOD

def closure(gens, n):
    I = eye_t(n); seen = {I}; q = deque([I])
    while q:
        g = q.popleft()
        for s in gens:
            h = mm_t(s, g, n)
            if h not in seen: seen.add(h); q.append(h)
    return seen

J = np.array([[0,1,0,0],[-1,0,0,0],[0,0,0,1],[0,0,-1,0]], dtype=int) % MOD

def symp(u, v):
    return int((np.array(u,dtype=int) @ J @ np.array(v,dtype=int)) % MOD)

pairs = [(0,1),(0,2),(0,3),(1,2),(1,3),(2,3)]
def wedge_vec(u, v):
    u = np.array(u,dtype=int) % MOD; v = np.array(v,dtype=int) % MOD
    return np.array([(u[i]*v[j] - u[j]*v[i]) % MOD for i,j in pairs], dtype=int)

def qprim(x):
    a,b,c,d,e = map(int,x)
    return (-a*a - b*e + c*d) % MOD

V4 = list(product(range(3), repeat=4))
raw_punctured = [v for v in V4 if any(v)]
assert len(raw_punctured) == 80

derived80 = set()
for u in V4:
    for v in V4:
        if symp(u,v) == 0:
            p = wedge_vec(u,v)
            assert (int(p[0]) + int(p[5])) % MOD == 0
            assert (int(p[0])*int(p[5]) - int(p[1])*int(p[4]) + int(p[2])*int(p[3])) % MOD == 0
            z = tuple(int(x) for x in p[:5])
            if any(z):
                assert qprim(z) == 0
                derived80.add(z)
null80 = {v for v in product(range(3), repeat=5) if any(v) and qprim(v) == 0}
assert len(derived80) == len(null80) == 80
assert derived80 == null80

def canon_line(v):
    v = tuple(int(x)%MOD for x in v); nv = tuple((-x)%MOD for x in v)
    return min(v,nv)
null_lines = sorted({canon_line(v) for v in null80})
assert len(null_lines) == 40

e5 = np.eye(5,dtype=int)
Bp = np.zeros((5,5),dtype=int)
for i in range(5):
    for j in range(5):
        Bp[i,j] = (qprim((e5[i]+e5[j])%MOD)-qprim(e5[i])-qprim(e5[j])) % MOD

def graph_stats(points, B):
    n = len(points); A = [[False]*n for _ in range(n)]
    for i,x in enumerate(points):
        X = np.array(x,dtype=int)
        for j,y in enumerate(points):
            if i != j and int(X @ B @ np.array(y,dtype=int)) % MOD == 0: A[i][j] = True
    degrees = {sum(row) for row in A}; lam=set(); mu=set()
    for i in range(n):
        for j in range(i+1,n):
            common = sum(A[i][k] and A[j][k] for k in range(n))
            (lam if A[i][j] else mu).add(common)
    return degrees,lam,mu
assert graph_stats(null_lines,Bp) == ({12},{2},{4})

def transvection(v):
    v = np.array(v,dtype=int).reshape(4,1) % MOD
    return (np.eye(4,dtype=int) + v @ (J @ v).T) % MOD
sp_vectors=[(1,0,0,0),(0,1,0,0),(0,0,1,0),(0,0,0,1),(1,0,1,0)]
sp_gens=[tmat(transvection(v)) for v in sp_vectors]
Sp4=closure(sp_gens,4); assert len(Sp4)==51840
anti=np.diag([1,2,1,2])%MOD
assert np.array_equal((anti.T@J@anti)%MOD,(2*J)%MOD)
GSp4=closure(sp_gens+[tmat(anti)],4); assert len(GSp4)==103680

P6=np.zeros((6,5),dtype=int); P6[0,0]=1; P6[5,0]=2
for col,row in enumerate([1,2,3,4],start=1): P6[row,col]=1

def wedge6_matrix(g):
    G=np.array(g,dtype=int).reshape(4,4)%MOD
    return np.stack([wedge_vec(G[:,i],G[:,j]) for i,j in pairs],axis=1)%MOD

def primitive5_action(g):
    images=(wedge6_matrix(g)@P6)%MOD
    assert np.all(images[5,:]==(-images[0,:])%MOD)
    return tmat(images[:5,:])
pgsp_image={primitive5_action(g) for g in GSp4}
psp_image={primitive5_action(g) for g in Sp4}
assert len(pgsp_image)==51840 and len(psp_image)==25920
I4=eye_t(4); minusI4=tmat(2*np.eye(4,dtype=int)); I5=eye_t(5)
assert {g for g in GSp4 if primitive5_action(g)==I5} == {I4,minusI4}

Cint=2*np.eye(6,dtype=int)
for i,j in [(0,1),(1,2),(2,3),(3,4),(2,5)]: Cint[i,j]=Cint[j,i]=-1
C=Cint%MOD; assert rank_mod(C)==5
rad=[v for v in product(range(3),repeat=6) if any(v) and np.all((C@np.array(v,dtype=int))%MOD==0)]
assert len(rad)==2
r=np.array(rad[0],dtype=int).reshape(6,1); std=np.eye(6,dtype=int); Q=None
for comb in combinations(range(6),5):
    candidate=np.column_stack([std[:,i] for i in comb]); M=np.column_stack([candidate,r[:,0]])
    if rank_mod(M)==6: Q=candidate%MOD; break
assert Q is not None
M=np.column_stack([Q,r[:,0]])%MOD; proj=inv_mod(M)[:5,:]%MOD; Be=(Q.T@C@Q)%MOD

e6_gens=[]
for i in range(6):
    ei=np.eye(6,dtype=int)[:,[i]]; Si=(np.eye(6,dtype=int)-ei@C[i,:].reshape(1,6))%MOD
    Gi=(proj@Si@Q)%MOD; assert np.array_equal((Gi.T@Be@Gi)%MOD,Be); e6_gens.append(tmat(Gi))
WE6=closure(e6_gens,5); assert len(WE6)==51840

vectors5=[np.array(v,dtype=int) for v in product(range(3),repeat=5)]
def bil(x,y): return int(x@Bp@y)%MOD
candidates={n:[v for v in vectors5 if bil(v,v)==n] for n in range(3)}; cols=[]
def find_isometry(k=0):
    if k==5: return np.column_stack(cols)%MOD
    for v in candidates[int(Be[k,k])]:
        if all(bil(cols[j],v)==int(Be[j,k]) and bil(v,cols[j])==int(Be[k,j]) for j in range(k)):
            cols.append(v); out=find_isometry(k+1)
            if out is not None: return out
            cols.pop()
    return None
T=find_isometry(); assert T is not None and np.array_equal((T.T@Bp@T)%MOD,Be); Tinv=inv_mod(T)
WE6p={tmat((T@np.array(g,dtype=int).reshape(5,5)@Tinv)%MOD) for g in WE6}
assert WE6p==pgsp_image

def refl_int(x,i):
    x=np.array(x,dtype=int); ei=np.eye(6,dtype=int)[:,i]
    return x-int(Cint[i,:]@x)*ei
roots={tuple(np.eye(6,dtype=int)[:,0])}; q=deque(roots)
while q:
    x=np.array(q.popleft(),dtype=int)
    for i in range(6):
        y=tuple(refl_int(x,i).tolist())
        if y not in roots: roots.add(y); q.append(y)
assert len(roots)==72
root_primitive=[]
for root in roots:
    qe=(proj@(np.array(root,dtype=int)%MOD))%MOD; z=(T@qe)%MOD
    root_primitive.append(tuple(int(a) for a in z))
assert len(set(root_primitive))==72 and {qprim(z) for z in root_primitive}=={1}
root_lines=sorted({canon_line(v) for v in root_primitive}); assert len(root_lines)==36
assert graph_stats(root_lines,Bp)==({15},{6},{6})

print("PASS f3/e6 exterior-square max-cut")
print("raw T4^x:",len(raw_punctured))
print("derived oriented Lagrangian/null carrier:",len(derived80))
print("projective null points:",len(null_lines),"SRG(40,12,2,4)")
print("|Sp4(3)|:",len(Sp4),"|GSp4(3)|:",len(GSp4))
print("|PSp image|:",len(psp_image),"|PGSp image|:",len(pgsp_image))
print("|W(E6) mod-3 image|:",len(WE6))
print("PGSp image == W(E6) image:",WE6p==pgsp_image)
print("E6 root lines:",len(root_lines),"SRG(36,15,6,6)")
