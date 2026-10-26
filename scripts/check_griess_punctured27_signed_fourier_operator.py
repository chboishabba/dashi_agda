#!/usr/bin/env python3
"""Exact native punctured P3^3 Fourier parity and signed quotient spectrum.

Roots: Agda #1249 native cube/antipode, Agda #1261 punctured 13 axes;
Lean #52 Griess source grade order13; classical Gross/Gross-Tucker
signed double-cover/voltage graphs and spectral linear algebra.
Python PASS != Lean or Agda kernel; no Albert-product or physical weld.
"""
from itertools import product
import sympy as s
V=tuple(p for p in product((-1,0,1),repeat=3) if p!=(0,0,0))
neg=lambda p:tuple(-x for x in p)
R=tuple(sorted({min(p,neg(p)) for p in V}))
idx={p:i for i,p in enumerate(V)}
E=lambda a,b:sum(abs(x-y) for x,y in zip(a,b))==1
A=s.Matrix(26,26,lambda i,j:int(E(V[i],V[j])))
U=s.Matrix(13,13,lambda i,j:int(E(R[i],R[j])))
W=s.Matrix(13,13,lambda i,j:int(E(R[i],neg(R[j]))))
P,M=U+W,U-W
assert len(V)==26 and len(R)==13 and sum(int(x) for x in A)==96
assert all(U[i,j]+W[i,j]<=1 for i,j in product(range(13),repeat=2))
H=s.zeros(26,26)
for j,p in enumerate(R):
 H[idx[p],j]=H[idx[neg(p)],j]=H[idx[p],j+13]=1
 H[idx[neg(p)],j+13]=-1
assert H.T*H==2*s.eye(26)
assert A*H==H*s.diag(P,M)
assert H.T*A*H/2==s.diag(P,M)
odd=[i for i,p in enumerate(R) if sum(x!=0 for x in p)%2]
face=[i for i,p in enumerate(R) if sum(x!=0 for x in p)==2]
assert (len(odd),len(face))==(7,6)
Bp=P.extract(odd,face);Bm=M.extract(odd,face)
Gp,Gm=Bp.T*Bp,Bm.T*Bm
assert Gp==2*s.eye(6)+2*s.ones(6,6)
assert Gm**2==8*Gm and s.trace(Gm)==24
assert (P.rank(),M.rank(),A.rank())==(12,6,18)
x=s.Symbol('x')
cp=s.factor(P.charpoly(x).as_expr())
cm=s.factor(M.charpoly(x).as_expr())
ca=s.factor(A.charpoly(x).as_expr())
assert s.expand(cp-x*(x*x-14)*(x*x-2)**5)==0
assert s.expand(cm-x**7*(x*x-8)**3)==0
assert s.expand(ca-cp*cm)==0
def word(p):
 z=[a%3 for a in p]
 for i,j in ((0,1),(1,2),(2,0)):z[i]=(z[i]+z[j])%3
 return tuple(a if a!=2 else -1 for a in z)
perm=s.Matrix(26,26,lambda i,j:int(V[i]==word(V[j])))
assert perm.T*perm==s.eye(26) and perm**13==s.eye(26)
assert s.trace(A*(perm.T*A*perm))==0
assert sum(q*q for q in (perm.T*A*perm-A))==192
C=lambda p:min(p,neg(p))
proj=s.Matrix(13,13,lambda i,j:int(R[i]==C(word(R[j]))))
assert proj**13==s.eye(13)
assert s.trace(P*(proj.T*P*proj))==10
assert sum(q*q for q in (proj.T*P*proj-P))==76
print('PASS actual 26x26 spatial adjacency A H=H diag(even13,odd13), H.T H=2I')
print('PASS actual 7x6 blocks Bplus.T Bplus=2I+2J; signed Gram square=8 Gram, trace=24')
print('PASS charpolys:',cp,';',cm,';',ca)
print('PASS ranks 12+6=18, nullities 1+7=8')
print('PASS actual Griess 13-cycle: 0/48 spatial edges retained; graph Frobenius²=192')
print('PASS projective quotient 5/24 edges retained; graph Frobenius²=76')
print('UNPAID: Lean/Agda kernel, actual Monster 3B or physical graph action')
