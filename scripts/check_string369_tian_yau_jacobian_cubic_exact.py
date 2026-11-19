#!/usr/bin/env python3
"""Selected Tian-Yau multigraded Jacobian cubic, exact rational ranks.

Classical: Candelas, Yukawa Couplings Between (2,1)-Forms, NPB 298
(1988) 458-492; Cayley auxiliary polynomial and residue methods.
Original Johl Brown/DASHI: selected smooth/free G,H,F in PR #1531,
first-Tits E6 cubic #1106, KK #1241 and C3/zeta-square owners.
New: literal selected-equation quotient and invariant cubic ranks.
Raw ring degree 2 has extra dimension: geometric residue comparison
and normalization are NOT claimed or replaced by matching dimensions.
"""
from itertools import combinations_with_replacement
from functools import lru_cache
from fractions import Fraction as Q
import sympy as s

@lru_cache(None)
def comps(n,k):
    if k==1:return [(n,)] if n>=0 else []
    return [(i,)+r for i in range(n+1) for r in comps(n-i,k-1)]
D=((3,0),(0,3),(1,1))
deg=[(0,1,0)]*4+[(0,0,1)]*4+[(1,-a,-b) for a,b in D]
@lru_cache(None)
def mons(d,a,b):
    return [x+y+u for u in comps(d,3)
            for x in comps(a+3*u[0]+u[2],4)
            for y in comps(b+3*u[1]+u[2],4)]
v=s.symbols('x0:4')+s.symbols('y0:4')+s.symbols('u0:3')
x=v[:4];y=v[4:8];u=v[8:]
G=sum(t**3 for t in x)-x[1]*x[2]*x[3]
H=G.xreplace(dict(zip(x,y)))
F=sum(a*b for a,b in zip(x,y))
W=sum(a*b for a,b in zip(u,(G,H,F)))
J=[s.Poly(s.diff(W,t),*v).terms() for t in v]
def rows(d):
    ms=mons(d,0,0);ix={m:i for i,m in enumerate(ms)}
    for j,(k,a,b) in zip(J,deg):
        for m in mons(d-1+k,a,b):
            yield {ix[tuple(a+b for a,b in zip(m,e))]:int(c) for e,c in j}
def rational(d):
    basis={}
    for r in rows(d):
        r={k:Q(v) for k,v in r.items()}
        while r:
            j=min(r);c=r[j]
            if j not in basis:
                basis[j]={k:v/c for k,v in r.items()};break
            for k,v in basis[j].items():
                z=r.get(k,0)-c*v
                if z:r[k]=z
                elif k in r:del r[k]
    return basis
def modular(d,p):
    basis={}
    for r in rows(d):
        while r:
            j=min(r);c=r[j]%p
            if not c:del r[j];continue
            if j not in basis:
                inv=pow(c,-1,p)
                basis[j]={k:v*inv%p for k,v in r.items() if v%p};break
            for k,v in basis[j].items():
                z=(r.get(k,0)-c*v)%p
                if z:r[k]=z
                elif k in r:del r[k]
    return len(mons(d,0,0))-len(basis)
def quotient(d,B):
    ms=mons(d,0,0);free=[i for i in range(len(ms)) if i not in B];out={}
    for i in reversed(range(len(ms))):
        if i in B:
            out[i]=[sum(-c*out[j][k] for j,c in B[i].items() if j!=i)
                    for k in range(len(free))]
        else:out[i]=[Q(int(i==j)) for j in free]
    return ms,free,out
assert [modular(d,101) for d in (1,2,3)]==[23,24,1]
m1,f1,r1=quotient(1,rational(1))
m3,f3,r3=quotient(3,rational(3))
assert (len(m1),len(f1),len(m3),len(f3))==(56,23,7505,1)
idx3={m:i for i,m in enumerate(m3)}
idx1={m:i for i,m in enumerate(m1)}
basis=[m1[j] for j in f1];n=len(basis)
def cyc(m):
    return (m[0],m[3],m[1],m[2],m[4],m[7],m[5],m[6])+m[8:]
P=s.Matrix.hstack(*(s.Matrix(r1[idx1[cyc(m)]]) for m in basis))
assert P**3==s.eye(n) and P.trace()==2
C=(s.eye(n)+P+P**2)/3
I=C.columnspace();U=(s.eye(n)-C).columnspace()
assert (len(I),len(U))==(9,14)
def coeff(i,j,k):
    m=tuple(a+b+c for a,b,c in zip(basis[i],basis[j],basis[k]))
    return r3[idx3[m]][0]
T=[s.Matrix(n,n,lambda j,k:coeff(i,j,k)) for i in range(n)]
for i in range(n):
    assert P.T*sum((P[j,i]*T[j] for j in range(n)),s.zeros(n))*P==T[i]
V=s.Matrix.hstack(*U)
def slice(w):return sum((w[j]*T[j] for j in range(n)),s.zeros(n))
ranks=[(V.T*slice(w)*V).rank() for w in I]
assert ranks==[14,12,12,14,14,14,14,12,12]
w=sum(I,s.zeros(n,1));M=V.T*slice(w)*V
assert M.rank()==14
assert M.det()!=0
assert sum(coeff(*ijk)!=0 for ijk in combinations_with_replacement(range(n),3))==272
assert m3[f3[0]]==(9,0,0,0,0,0,0,0,3,0,0)
print('PASS exact Q degree 1 and 3 quotient dimensions 23,1')
print('PASS F101 degree 1,2,3 quotient dimensions 23,24,1')
print('PASS 272 nonzero unordered cubic coefficients; all C3 equivariance identities')
print('PASS invariant slices on nontrivial sector ranks',ranks)
print('PASS sum slice determinant',M.det())
print('OPEN geometric residue comparison, matter metric, full F/D-flat vacuum')
