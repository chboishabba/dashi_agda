#!/usr/bin/env python3
"""Exact finite linear-algebra probe for the rational octonion/Albert max-cut.

This script mirrors the repository's Cayley--Dickson convention and the explicit
Albert Jordan product.  It is diagnostic authority, not Agda kernel authority.
It checks:

* the signed imaginary-basis octonion automorphism group has order 1344;
* two explicit generators (orders 7 and 4) generate all 1344 automorphisms;
* the 21 standard octonion derivations
    D_ab = [L_a,L_b] + [L_a,R_b] + [R_a,R_b]
  satisfy the derivation law on basis products and span rank 14;
* the 351 Albert inner derivations [L_X,L_Y] span rank 52 and satisfy the
  derivation commutator identity on the 27-coordinate basis.
"""

from collections import deque
from itertools import permutations, product
import sympy as sp


def qmul(a,b):
    a0,a1,a2,a3=a; b0,b1,b2,b3=b
    return (a0*b0-a1*b1-a2*b2-a3*b3,
            a0*b1+a1*b0+a2*b3-a3*b2,
            a0*b2-a1*b3+a2*b0+a3*b1,
            a0*b3+a1*b2-a2*b1+a3*b0)

def qconj(a): return (a[0],-a[1],-a[2],-a[3])
def qadd(a,b): return tuple(x+y for x,y in zip(a,b))
def qneg(a): return tuple(-x for x in a)
ZQ=(0,0,0,0)

def omul(x,y):
    a,b=x; c,d=y
    return (qadd(qmul(a,c),qneg(qmul(qconj(d),b))),
            qadd(qmul(d,a),qmul(b,qconj(c))))

QS=[(1,0,0,0),(0,1,0,0),(0,0,1,0),(0,0,0,1)]
B=[(QS[i],ZQ) for i in range(4)]+[(ZQ,QS[i]) for i in range(4)]

def ident(x):
    for i,b in enumerate(B):
        if x==b: return (1,i)
        if x==(qneg(b[0]),qneg(b[1])): return (-1,i)
    raise ValueError(x)

TABLE={(i,j):ident(omul(B[i],B[j])) for i in range(8) for j in range(8)}

def signed_basis_auto(perm, signs):
    for i in range(1,8):
        for j in range(1,8):
            if i==j: continue
            s,k=TABLE[i,j]
            lhs=(s*signs[k],perm[k])
            s2,k2=TABLE[perm[i],perm[j]]
            rhs=(signs[i]*signs[j]*s2,k2)
            if lhs!=rhs: return False
    return True

AUTOS=[]
for pt in permutations(range(1,8)):
    perm={i:pt[i-1] for i in range(1,8)}
    for st in product((1,-1),repeat=7):
        signs={i:st[i-1] for i in range(1,8)}
        if signed_basis_auto(perm,signs): AUTOS.append((pt,st))
assert len(AUTOS)==1344

ID=(tuple(range(1,8)),(1,)*7)
def compose(A,B):
    pA,sA=A; pB,sB=B
    return (tuple(pA[pB[i-1]-1] for i in range(1,8)),
            tuple(sB[i-1]*sA[pB[i-1]-1] for i in range(1,8)))
def order(A):
    x=ID
    for n in range(1,100):
        x=compose(A,x)
        if x==ID:return n
    raise AssertionError

g7=((2,4,6,3,1,7,5),(1,1,1,1,1,-1,-1))
g4=((1,2,3,5,4,7,6),(1,1,1,1,-1,1,-1))
assert g7 in AUTOS and g4 in AUTOS and order(g7)==7 and order(g4)==4
seen={ID}; q=deque([ID])
while q:
    x=q.popleft()
    for g in (g7,g4):
        y=compose(g,x)
        if y not in seen: seen.add(y); q.append(y)
assert len(seen)==1344

# Linear octonion model.
def tovec(x): return list(x[0])+list(x[1])
def fromvec(v): return (tuple(v[:4]),tuple(v[4:]))
def oadd(x,y): return (qadd(x[0],y[0]),qadd(x[1],y[1]))
def oneg(x): return (qneg(x[0]),qneg(x[1]))
def osub(x,y): return oadd(x,oneg(y))

def Dpair(a,b,x):
    LaLb=omul(a,omul(b,x)); LbLa=omul(b,omul(a,x))
    LaRb=omul(a,omul(x,b)); RbLa=omul(omul(a,x),b)
    RaRb=omul(omul(x,b),a); RbRa=omul(omul(x,a),b)
    return oadd(oadd(osub(LaLb,LbLa),osub(LaRb,RbLa)),osub(RaRb,RbRa))

DMATS=[]
for i in range(1,8):
    for j in range(i+1,8):
        M=sp.Matrix.hstack(*[sp.Matrix(tovec(Dpair(B[i],B[j],B[k]))) for k in range(8)])
        DMATS.append(M)
        for p in range(8):
            for r in range(8):
                lhs=M*sp.Matrix(tovec(omul(B[p],B[r])))
                rhs=sp.Matrix(tovec(omul(fromvec(list(M[:,p])),B[r])))+sp.Matrix(tovec(omul(B[p],fromvec(list(M[:,r])))))
                assert lhs==rhs
Dflat=sp.Matrix.hstack(*[M.reshape(64,1) for M in DMATS])
assert Dflat.rank()==14

# Albert product from the repository coordinate formula.
def omv(u,v):
    out=[sp.Rational(0) for _ in range(8)]
    for i,ui in enumerate(u):
        if ui==0: continue
        for j,vj in enumerate(v):
            if vj==0: continue
            s,k=TABLE[i,j]; out[k]+=ui*vj*s
    return sp.Matrix(out)
def oconjv(u): return sp.Matrix([u[0]]+[-u[i] for i in range(1,8)])
def oinner(u,v): return omv(u,oconjv(v))[0]

def aprod(X,Y):
    a,b,c=X[0],X[1],X[2]; x=sp.Matrix(X[3:11]); y=sp.Matrix(X[11:19]); z=sp.Matrix(X[19:27])
    ap,bp,cp=Y[0],Y[1],Y[2]; xp=sp.Matrix(Y[3:11]); yp=sp.Matrix(Y[11:19]); zp=sp.Matrix(Y[19:27])
    d0=a*ap+oinner(z,zp)+oinner(y,yp)
    d1=b*bp+oinner(z,zp)+oinner(x,xp)
    d2=c*cp+oinner(y,yp)+oinner(x,xp)
    ox=(omv(oconjv(z),oconjv(yp))+b*xp+cp*x+omv(oconjv(zp),oconjv(y))+bp*x+c*xp)/2
    oy=(ap*y+omv(oconjv(x),oconjv(zp))+c*yp+a*yp+omv(oconjv(xp),oconjv(z))+cp*y)/2
    oz=(a*zp+bp*z+omv(oconjv(y),oconjv(xp))+ap*z+b*zp+omv(oconjv(yp),oconjv(x)))/2
    return sp.Matrix([d0,d1,d2]+list(ox)+list(oy)+list(oz))

AB=[sp.eye(27)[:,i] for i in range(27)]
L=[sp.Matrix.hstack(*[aprod(AB[i],AB[j]) for j in range(27)]) for i in range(27)]
INNER=[L[i]*L[j]-L[j]*L[i] for i in range(27) for j in range(i+1,27)]
F=sp.Matrix.hstack(*[D.reshape(729,1) for D in INNER])
assert F.rank()==52
for D in INNER:
    for p in range(27):
        dp=D[:,p]
        Ldp=sp.zeros(27)
        for k,coef in enumerate(dp):
            if coef: Ldp += coef*L[k]
        assert D*L[p]-L[p]*D == Ldp

print("signed_basis_autos=1344")
print("g7_order=7 g4_order=4 generated=1344")
print("octonion_inner_derivation_span_rank=14")
print("albert_inner_derivation_span_rank=52")
print("all_basis_derivation_checks=PASS")
