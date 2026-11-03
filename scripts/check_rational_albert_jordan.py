#!/usr/bin/env python3
"""Exact Fraction preflight for the repo-native rational Albert construction.

This mirrors the Cayley-Dickson convention already proved in
CayleyDicksonRationalOctonionExact.agda and checks the new
RationalAlbertJordanExact.agda formulas.

Execution evidence only, not an Agda kernel proof.  It checks:
* repo octonion associator orientation (e1 e2)e4 = e7, e1(e2 e4) = -e7;
* Hermitian closure of X o Y = (XY+YX)/2;
* unit laws on basis and randomized points;
* Jordan identity on all 27 coordinate basis-pair cases and deterministic
  randomized cases;
* cubic characteristic identity on deterministic randomized points.
"""

from fractions import Fraction as F
import random

ZERO4 = (F(0),) * 4


def qadd(a,b): return tuple(x+y for x,y in zip(a,b))
def qneg(a): return tuple(-x for x in a)
def qsub(a,b): return qadd(a,qneg(b))
def qconj(a): return (a[0],-a[1],-a[2],-a[3])
def qmul(a,b):
    w,x,y,z=a; W,X,Y,Z=b
    return (w*W-x*X-y*Y-z*Z,
            w*X+x*W+y*Z-z*Y,
            w*Y-x*Z+y*W+z*X,
            w*Z+x*Y-y*X+z*W)


def oadd(x,y): return (qadd(x[0],y[0]),qadd(x[1],y[1]))
def oneg(x): return (qneg(x[0]),qneg(x[1]))
def oconj(x): return (qconj(x[0]),qneg(x[1]))
def omul(x,y):
    a,b=x; c,d=y
    return (qsub(qmul(a,c),qmul(qconj(d),b)),
            qadd(qmul(d,a),qmul(b,qconj(c))))
def ozero(): return (ZERO4,ZERO4)
def oscalar(s): return ((s,F(0),F(0),F(0)),ZERO4)
def oscale(s,x): return omul(oscalar(s),x)
def oreal(x): return x[0][0]
def onorm(x): return sum(t*t for q in x for t in q)

def obasis(i):
    v=[F(0)]*8; v[i]=F(1)
    return (tuple(v[:4]),tuple(v[4:]))

HALF=F(1,2)

# Albert tuple: (a1,a2,a3,x1,x2,x3)
def matrix(A):
    a,b,c,x1,x2,x3=A
    return [[oscalar(a),x3,oconj(x2)],
            [oconj(x3),oscalar(b),x1],
            [x2,oconj(x1),oscalar(c)]]

def mmul(A,B):
    out=[]
    for i in range(3):
        row=[]
        for j in range(3):
            s=ozero()
            for k in range(3): s=oadd(s,omul(A[i][k],B[k][j]))
            row.append(s)
        out.append(row)
    return out

def from_hermitian(M):
    assert M[1][0]==oconj(M[0][1])
    assert M[2][0]==oconj(M[0][2])
    assert M[2][1]==oconj(M[1][2])
    for i in range(3): assert M[i][i]==oscalar(oreal(M[i][i]))
    return (oreal(M[0][0]),oreal(M[1][1]),oreal(M[2][2]),M[1][2],M[2][0],M[0][1])

def jordan(A,B):
    X,Y=matrix(A),matrix(B)
    XY,YX=mmul(X,Y),mmul(Y,X)
    S=[[oscale(HALF,oadd(XY[i][j],YX[i][j])) for j in range(3)] for i in range(3)]
    return from_hermitian(S)

def addA(A,B): return tuple([A[i]+B[i] for i in range(3)]+[oadd(A[i],B[i]) for i in range(3,6)])
def scaleA(s,A): return tuple([s*A[i] for i in range(3)]+[oscale(s,A[i]) for i in range(3,6)])
def zeroA(): return (F(0),F(0),F(0),ozero(),ozero(),ozero())
def traceA(A): return A[0]+A[1]+A[2]
def normA(A):
    a,b,c,x1,x2,x3=A
    p=omul(omul(x1,x2),x3)
    return a*b*c-a*onorm(x1)-b*onorm(x2)-c*onorm(x3)+oreal(oadd(p,oconj(p)))

UNIT=(F(1),F(1),F(1),ozero(),ozero(),ozero())

def basis27():
    out=[]
    for d in range(3):
        a=[F(0),F(0),F(0)]; a[d]=F(1)
        out.append((a[0],a[1],a[2],ozero(),ozero(),ozero()))
    for slot in range(3):
        for k in range(8):
            xs=[ozero(),ozero(),ozero()]; xs[slot]=obasis(k)
            out.append((F(0),F(0),F(0),xs[0],xs[1],xs[2]))
    assert len(out)==27
    return out

def jordan_identity(X,Y):
    X2=jordan(X,X)
    return jordan(jordan(X2,Y),X)==jordan(X2,jordan(Y,X))

def characteristic_identity(X):
    X2=jordan(X,X); X3=jordan(X2,X)
    tr=traceA(X)
    s=F(1,2)*(tr*tr-traceA(X2))
    value=addA(addA(X3,scaleA(-tr,X2)),addA(scaleA(s,X),scaleA(-normA(X),UNIT)))
    return value==zeroA()

def random_oct(rng):
    q=[F(rng.randint(-2,2)) for _ in range(8)]
    return (tuple(q[:4]),tuple(q[4:]))

def random_albert(rng):
    return (F(rng.randint(-2,2)),F(rng.randint(-2,2)),F(rng.randint(-2,2)),
            random_oct(rng),random_oct(rng),random_oct(rng))

def main():
    e1,e2,e4,e7=obasis(1),obasis(2),obasis(4),obasis(7)
    assert omul(omul(e1,e2),e4)==e7
    assert omul(e1,omul(e2,e4))==oneg(e7)

    basis=basis27()
    for x in basis:
        assert jordan(UNIT,x)==x==jordan(x,UNIT)
    for x in basis:
        for y in basis:
            assert jordan_identity(x,y)

    rng=random.Random(36927)
    for _ in range(100):
        x,y=random_albert(rng),random_albert(rng)
        assert jordan(UNIT,x)==x==jordan(x,UNIT)
        assert jordan_identity(x,y)
    for _ in range(30):
        assert characteristic_identity(random_albert(rng))

    print("Albert dimension basis    = 27")
    print("basis-pair Jordan tests   = 729 exact")
    print("random Jordan tests       = 100 exact")
    print("characteristic tests      = 30 exact")
    print("RUN_TERMINAL COMPLETE")

if __name__ == '__main__':
    main()
