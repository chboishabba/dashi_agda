#!/usr/bin/env python3
"""Exact rational diagnostic for the Albert inner-derivation Lie algebra.

Uses the repository coordinate convention for H_3(O_Q) and its Jordan product.
It constructs all D_ij=[L_ei,L_ej] on the 27 coordinate basis and reports:

  * all 351 D_ij satisfy the derivation identity;
  * their span has dimension 52;
  * an explicit 52-element pivot basis;
  * commutator closure has dimension 52;
  * the derived algebra has dimension 52;
  * the center has dimension 0.

This script is an exact SymPy/Q diagnostic.  It does not by itself classify the
resulting Lie algebra as type F4.
"""
from fractions import Fraction as F
import sympy as sp


def qmul(a,b):
    w,x,y,z=a; W,X,Y,Z=b
    return (w*W-x*X-y*Y-z*Z,
            w*X+x*W+y*Z-z*Y,
            w*Y-x*Z+y*W+z*X,
            w*Z+x*Y-y*X+z*W)

def qconj(a): return (a[0],-a[1],-a[2],-a[3])
def qadd(a,b): return tuple(x+y for x,y in zip(a,b))
def qneg(a): return tuple(-x for x in a)

def omul(o,p):
    a,b=o; c,d=p
    return (qadd(qmul(a,c),qneg(qmul(qconj(d),b))),
            qadd(qmul(d,a),qmul(b,qconj(c))))

def oadd(x,y): return qadd(x[0],y[0]),qadd(x[1],y[1])
def oscale(s,x): return tuple(s*a for a in x[0]),tuple(s*a for a in x[1])
def oconj(x): return qconj(x[0]),qneg(x[1])
def flat(x): return x[0]+x[1]
def real(x): return x[0][0]
def inner(x,y): return real(omul(x,oconj(y)))

def jordan(X,Y):
    a,b,c,x,y,z=X; d,e,f,u,v,w=Y
    d0=a*d+inner(z,w)+inner(y,v)
    d1=b*e+inner(z,w)+inner(x,u)
    d2=c*f+inner(y,v)+inner(x,u)
    ox=oscale(F(1,2),oadd(oadd(oadd(omul(oconj(z),oconj(v)),oscale(b,u)),oscale(f,x)),
                              oadd(oadd(omul(oconj(w),oconj(y)),oscale(e,x)),oscale(c,u))))
    oy=oscale(F(1,2),oadd(oadd(oadd(oscale(d,y),omul(oconj(x),oconj(w))),oscale(c,v)),
                              oadd(oadd(oscale(a,v),omul(oconj(u),oconj(z))),oscale(f,y))))
    oz=oscale(F(1,2),oadd(oadd(oadd(oscale(a,w),oscale(e,z)),omul(oconj(y),oconj(u))),
                              oadd(oadd(oscale(d,z),oscale(b,w)),omul(oconj(v),oconj(x)))))
    return d0,d1,d2,ox,oy,oz

def alb(v):
    o=lambda a:(tuple(F(x) for x in a[:4]),tuple(F(x) for x in a[4:]))
    return F(v[0]),F(v[1]),F(v[2]),o(v[3:11]),o(v[11:19]),o(v[19:27])

def vec(X): return [X[0],X[1],X[2],*flat(X[3]),*flat(X[4]),*flat(X[5])]

def smat(q): return sp.Rational(q.numerator,q.denominator)

E=[]
for i in range(27):
    v=[F(0)]*27; v[i]=F(1); E.append(alb(v))

L=[]
for i in range(27):
    cols=[vec(jordan(E[i],E[j])) for j in range(27)]
    L.append(sp.Matrix([[smat(cols[c][r]) for c in range(27)] for r in range(27)]))

pairs=[]; D=[]
for i in range(27):
    for j in range(i+1,27):
        pairs.append((i,j)); D.append(L[i]*L[j]-L[j]*L[i])

def flatten(M): return sp.Matrix(M).reshape(729,1)
span=sp.Matrix.hstack(*map(flatten,D))
rank=span.rank()
_,piv=span.rref()
basis=[D[i] for i in piv]
pivot_pairs=[pairs[i] for i in piv]

# Derivation identity [D,L_x]=L_{Dx} on the basis.
def is_derivation(T):
    for i in range(27):
        rhs=sp.zeros(27)
        for k in range(27):
            if T[k,i]: rhs += T[k,i]*L[k]
        if T*L[i]-L[i]*T != rhs: return False
    return True

derivation_count=sum(is_derivation(T) for T in D)

comm=[]
for i in range(len(basis)):
    for j in range(i+1,len(basis)):
        comm.append(basis[i]*basis[j]-basis[j]*basis[i])
comm_rank=sp.Matrix.hstack(*map(flatten,comm)).rank()
combined_rank=sp.Matrix.hstack(span,*map(flatten,comm)).rank()

# Center of the selected 52-dimensional Lie algebra.
blocks=[]
for j in range(len(basis)):
    blocks.append(sp.Matrix.hstack(*[flatten(basis[i]*basis[j]-basis[j]*basis[i])
                                     for i in range(len(basis))]))
center_equations=sp.Matrix.vstack(*blocks)
center_dim=len(basis)-center_equations.rank()

print('pair derivations:',len(D))
print('derivations passing identity:',derivation_count)
print('inner derivation span dimension:',rank)
print('pivot pairs:',pivot_pairs)
print('commutator span dimension:',comm_rank)
print('combined span dimension:',combined_rank)
print('center dimension:',center_dim)

assert derivation_count==351
assert rank==52
assert len(piv)==52
assert comm_rank==52
assert combined_rank==52
assert center_dim==0
