"""Exact source-axis jets; rational Bernstein range enclosures."""
from fractions import Fraction as Q
from math import comb,factorial
import sympy as s
import numpy as np
from check_hopf369_p0bn import I,J,idx,zero

def coefficients():
    X=s.symbols('x0:3');t,r=s.symbols('t r');h=s.Rational(4,5);eps=s.Rational(1,40);d=1-t;F=2*(1+t)/h;den=d**4+F**2*t;x=s.Matrix(X)
    all_={}
    for e_axis in (0,1):
        e=s.eye(3)[:,e_axis];W=(d**4-F**2*t)*e+2*F**2*e.dot(x)*x+2*F*d*d*e.cross(x)
        initial=eps*h*(F*d*W+(4*d/h+4*F)*x*x.dot(W));cache={(i,(0,0,0)):s.Poly(initial[i],*X,t) for i in range(3)}
        D=s.Poly(den,*X,t);Dt=D.diff(t)
        for a in idx[3]:
            if a[3]:continue
            p=2+sum(a);b=a[:3];sub={X[0]:r,X[1]:0,X[2]:0,t:r*r}
            for i in range(3):
                if sum(b):
                    k=next(k for k in range(3) if b[k]);bb=list(b);bb[k]-=1;v=cache[i,tuple(bb)];xx=s.Poly(2*X[k],*X,t)
                    cache[i,b]=D*(v.diff(X[k])+xx*v.diff(t))-(p-1)*v*xx*Dt
                # evaluate without huge expression substitution
                terms={}
                for (a0,a1,a2,at),c in cache[i,b].terms():
                    if a1==a2==0:terms[a0+2*at]=terms.get(a0+2*at,0)+c
                P=s.Poly.from_dict({(k,):v for k,v in terms.items()},r,domain=s.QQ)
                P=P.mul_ground(s.Rational(1,int(np.prod([factorial(k) for k in b]))));D1=s.Poly(den.subs(t,r*r),r)**p
                G=s.gcd(P,D1);P=P.exquo(G);D1=D1.exquo(G)
                if D1.eval(0)<0:P=-P;D1=-D1
                all_[e_axis,i,a]=(P,D1)
    return all_

def bern(P,n):
    a=list(reversed(P.all_coeffs()));return [sum(Q(a[k])*Q(comb(j,k),comb(n,k)) for k in range(min(j,len(a)-1)+1)) for j in range(n+1)]
def split(b):
    L=[b[0]];R=[b[-1]]
    while len(b)>1:
        b=[(x+y)/2 for x,y in zip(b,b[1:])];L.append(b[0]);R.append(b[-1])
    return L,R[::-1]
def enclose(P,D,depth):
    if P.is_zero:return np.zeros((2**depth,2))
    n=max(P.degree(),D.degree());n=max(0,int(n));p=bern(P,n);d=bern(D,n)
    def rec(p,d,k):
        if k==0:
            assert min(d)>0
            a=[x/y for x,y in zip(p,d)];return [(min(a),max(a))]
        a,b=split(p);c,e=split(d);return rec(a,c,k-1)+rec(b,e,k-1)
    vals=rec(p,d,depth);return np.array([[np.nextafter(float(a),-np.inf),np.nextafter(float(b),np.inf)] for a,b in vals])

def bounds(depth=5):
    coeff=coefficients(); print('exact radial rational jets',len(coeff),flush=True)
    out={}
    for (e,i,a),(P,D) in coeff.items():out[str((e,i,a))]=enclose(P,D,depth)
    print('exact enclosed radial cells',2**depth,flush=True);return out

def source_jet(data,ri,angle):
    co=(1-angle**2)/(1+angle**2);si=2*angle/(1+angle**2)
    def one(i,a):
        v=data[str((0,i,a))][ri];w=data[str((1,i,a))][ri];return co*I(v[:,0],v[:,1])+si*I(w[:,0],w[:,1])
    return [J({a:one(i,a) for a in idx[3] if a[3]==0},3) for i in range(3)]
if __name__=='__main__':
    import sys
    bounds(int(sys.argv[1]) if len(sys.argv)>1 else 5)
