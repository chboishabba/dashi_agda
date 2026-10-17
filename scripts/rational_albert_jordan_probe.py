#!/usr/bin/env python3
"""Diagnostic exact-rational probe for the rational Albert coordinate product.

Mirrors DASHI/Mathematics/Algebra/RationalAlbertJordanProductExact.agda and the
repository Cayley-Dickson convention.  This is not Agda theorem authority.
"""

from fractions import Fraction as F
import random


def qadd(a,b): return tuple(x+y for x,y in zip(a,b))
def qneg(a): return tuple(-x for x in a)
def qconj(a): return (a[0],-a[1],-a[2],-a[3])
def qmul(a,b):
    w,x,y,z=a; W,X,Y,Z=b
    return (w*W-x*X-y*Y-z*Z,
            w*X+x*W+y*Z-z*Y,
            w*Y-x*Z+y*W+z*X,
            w*Z+x*Y-y*X+z*W)

Q0=(F(0),)*4

def oadd(o,p): return (qadd(o[0],p[0]),qadd(o[1],p[1]))
def oconj(o): return (qconj(o[0]),qneg(o[1]))
def omul(o,p):
    a,b=o; c,d=p
    # Repository convention: (a,b)(c,d)=(ac-conj(d)b, da+b conj(c)).
    first=qadd(qmul(a,c),qneg(qmul(qconj(d),b)))
    second=qadd(qmul(d,a),qmul(b,qconj(c)))
    return first,second

O0=(Q0,Q0)
def oscale(s,o): return (tuple(s*x for x in o[0]),tuple(s*x for x in o[1]))
def real(o): return o[0][0]
def inner(o,p): return real(omul(o,oconj(p)))
def osum(*xs):
    out=O0
    for x in xs: out=oadd(out,x)
    return out

HALF=F(1,2)

# Albert coordinate tuple = (a,b,c,x,y,z).
def jordan(X,Y):
    a,b,c,x,y,z=X
    A,B,C,u,v,w=Y
    d0=a*A+inner(z,w)+inner(y,v)
    d1=b*B+inner(z,w)+inner(x,u)
    d2=c*C+inner(y,v)+inner(x,u)
    ox=oscale(HALF,osum(omul(oconj(z),oconj(v)),oscale(b,u),oscale(C,x),
                         omul(oconj(w),oconj(y)),oscale(B,x),oscale(c,u)))
    oy=oscale(HALF,osum(oscale(A,y),omul(oconj(x),oconj(w)),oscale(c,v),
                         oscale(a,v),omul(oconj(u),oconj(z)),oscale(C,y)))
    oz=oscale(HALF,osum(oscale(a,w),oscale(B,z),omul(oconj(y),oconj(u)),
                         oscale(A,z),oscale(b,w),omul(oconj(v),oconj(x))))
    return d0,d1,d2,ox,oy,oz

UNIT=(F(1),F(1),F(1),O0,O0,O0)

def rand_o():
    c=[F(random.randint(-2,2)) for _ in range(8)]
    return tuple(c[:4]),tuple(c[4:])

def rand_a():
    return (F(random.randint(-2,2)),F(random.randint(-2,2)),F(random.randint(-2,2)),
            rand_o(),rand_o(),rand_o())

random.seed(369)
for _ in range(100):
    x=rand_a(); y=rand_a()
    assert jordan(x,UNIT)==x
    assert jordan(UNIT,x)==x
    assert jordan(x,y)==jordan(y,x)
    x2=jordan(x,x)
    assert jordan(jordan(x2,y),x)==jordan(x2,jordan(y,x))

print("100 exact-rational randomized cases: unit PASS")
print("100 exact-rational randomized cases: commutativity PASS")
print("100 exact-rational randomized cases: Jordan identity PASS")
