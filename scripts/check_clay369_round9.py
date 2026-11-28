"""Exact independent checks of the round9 finite mathematical constructions.
No native proof acceptance, PDE solution, Chow cycle or universal cost claim.
"""
from itertools import product
from fractions import Fraction as Q
from random import Random
import math
import sympy as s


def bsd():
    m,a,b,c,d,e,x,y=s.symbols('m a b c d e x y')
    X=(m*m+a*m-b-x)/2;Y=-y-a*x-c+m*(X-x)
    R=3*X**2+2*b*X+d-a*Y-m*(2*Y+a*X+c)
    F=lambda x,y:y*y+a*x*y+c*y-x**3-b*x*x-d*x-e
    quartic=m**4+2*a*m**3+(a*a-2*b-6*x)*m*m+(-2*a*b-10*a*x-4*c-8*y)*m-4*a*a*x-4*a*c-4*a*y+b*b-2*b*x-4*d-3*x*x
    assert s.expand(quartic+4*R)==0
    assert s.expand(F(X,Y)-F(x,y)-(x-X)*R)==0
    assert s.expand(m*m+a*m-b-2*X-x)==0
    assert s.expand(-Y-m*(x-X)-a*x-c-y)==0
    rng=Random(369);count=4;accepted=0
    for _ in range(500):
        a,b,c,d,X,Y=map(Q,(rng.randrange(-7,8) for _ in range(6)))
        e=Y*Y+a*X*Y+c*Y-X**3-b*X*X-d*X
        b2=a*a+4*b;b4=2*d+a*c;b6=c*c+4*e;b8=a*a*e+4*b*e-a*c*d+b*c*c-d*d
        if -b2*b2*b8-8*b4**3-27*b6*b6+9*b2*b4*b6==0:continue
        den=2*Y+a*X+c
        if not den:continue
        m=(3*X*X+2*b*X+d-a*Y)/den
        x=m*m+a*m-b-2*X;y=-Y-m*(x-X)-a*x-c
        assert F(x,y)==0;count+=1
        assert (m*m+a*m-b-x)/2==X;count+=1
        assert -y-a*x-c+m*(X-x)==Y;count+=1
        assert m**4+2*a*m**3+(a*a-2*b-6*x)*m*m+(-2*a*b-10*a*x-4*c-8*y)*m-4*a*a*x-4*a*c-4*a*y+b*b-2*b*x-4*d-3*x*x==0;count+=1
        accepted+=1
    return dict(bsd=count,bsd_examples=accepted)


def ns():
    # Gaussian rational coefficients, signed original R30.
    Z=(Q(0),Q(0));I=(Q(0),Q(1));zero=(0,0,0)
    def add(a,b):return a[0]+b[0],a[1]+b[1]
    def neg(a):return -a[0],-a[1]
    def mul(a,b):return a[0]*b[0]-a[1]*b[1],a[0]*b[1]+a[1]*b[0]
    def conj(a):return a[0],-a[1]
    def scale(a,c):return a[0]*c,a[1]*c
    def dot(k,u):
        z=Z
        for a,b in zip(k,u):z=add(z,scale(b,a))
        return z
    def project(k,u):
        n=sum(x*x for x in k)
        return tuple(add(v,scale(dot(k,u),-Q(a,n))) for a,v in zip(k,u)) if n else tuple(u)
    def pairing(u,v):return sum(mul(x,conj(y))[0] for x,y in zip(u,v))
    rng=Random(3699);count=0;states=0
    for N,reps in ((1,8),(2,1)):
        K=list(product(range(-N,N+1),repeat=3));ks=set(K)
        for _ in range(reps):
            U={zero:(Z,)*3}
            for k in K:
                if k not in U:
                    u=project(k,tuple((Q(rng.randrange(-3,4)),Q(rng.randrange(-3,4))) for _ in k));U[k]=u;U[tuple(-a for a in k)]=tuple(conj(v) for v in u)
            raw={};projected={};forces={k:[Z]*3 for k in K}
            for p,q in product(K,repeat=2):
                k=tuple(a+b for a,b in zip(p,q))
                if k not in ks:continue
                v=tuple(mul(neg(I),mul(dot(q,U[p]),x)) for x in U[q]);pv=project(k,v)
                raw[p,q]=pairing(v,U[k]);projected[p,q]=pairing(pv,U[k]);assert raw[p,q]==projected[p,q];count+=1
                forces[k]=list(map(add,forces[k],pv))
            for (p,q),w in raw.items():
                k=tuple(a+b for a,b in zip(p,q));assert raw[tuple(-a for a in p),k]==-w;count+=1
            assert sum(raw.values())==0;count+=1
            assert sum(pairing(forces[k],U[k]) for k in K)==0;count+=1
            nu=Q(3,7);D=sum(sum(x*x for x in k)*pairing(U[k],U[k]) for k in K)
            deriv=sum(2*pairing(tuple(add(scale(v,-nu*sum(x*x for x in k)),f) for v,f in zip(U[k],forces[k])),U[k]) for k in K)
            assert deriv==-2*nu*D;count+=1;states+=1
    return dict(ns=count,ns_states=states)


def hodge():
    masks=list(product((-1,1),repeat=6));count=0
    for bits in product((0,1),repeat=6):
        support=[i for i,v in enumerate(bits) if v]
        assert sum(math.prod(e)*math.prod(e[i] for i in support) for e in masks)==(64 if len(support)==6 else 0);count+=1
    rng=Random(3696)
    for _ in range(32):
        d=[Q(rng.randrange(1,12)*rng.choice((-1,1)),rng.randrange(1,8)) for _ in range(6)]
        for bits in product((0,1),repeat=6):
            support=[i for i,v in enumerate(bits) if v]
            assert sum(math.prod(e)*math.prod(e[i]*d[i] for i in support) for e in masks)==(64*math.prod(d) if len(support)==6 else 0);count+=1
    return dict(hodge=count)


def ym():
    rng=Random(36913);N=13**4;P=s.eye(12)/N;G=N*s.eye(12);count=0
    for _ in range(24):
        Ps=s.zeros(12);Pt=s.zeros(12);Pst=s.zeros(12)
        for i in range(11):
            Ps[i,i+1]=s.Rational(rng.randrange(-3,4),N);Pt[i+1,i]=s.Rational(rng.randrange(-3,4),N);Pst[i,i]=s.Rational(rng.randrange(-3,4),N)
        Gs=-G*Ps*G;Gt=-G*Pt*G;Gst=G*Ps*G*Pt*G+G*Pt*G*Ps*G-G*Pst*G
        assert G*Ps+Gs*P==s.zeros(12);count+=1
        assert P*Gs+Ps*G==s.zeros(12);count+=1
        assert G*Pst+Gs*Pt+Gt*Ps+Gst*P==s.zeros(12);count+=1
        assert P*Gst+Ps*Gt+Pt*Gs+Pst*G==s.zeros(12);count+=1
        B,Bs,Bt,Bst=[s.Matrix(12,3,lambda i,j:rng.randrange(-3,4)) for _ in range(4)];b=s.Matrix([1,-2,3])
        c=-G*B*b;cs=-(Gs*B+G*Bs)*b;ct=-(Gt*B+G*Bt)*b;cst=-(Gst*B+Gs*Bt+Gt*Bs+G*Bst)*b
        assert P*cst+Ps*ct+Pt*cs+Pst*c+Bst*b==s.zeros(12,1);count+=1
    return dict(ym=count)


if __name__=='__main__':
    if not __debug__:raise SystemExit('refusing optimized execution')
    result={**bsd(),**ns(),**hodge(),**ym()}
    total=sum(result[k] for k in ('bsd','ns','hodge','ym'))
    print(result,'TOTAL',total,'PASS')
