"""Exact rational signed Bernstein residual and causal energy recurrence.
All input jets are literal rational reconstruction data; no float quadrature.
"""
from fractions import Fraction as Q
from math import comb,isqrt
import json
import numpy as np
from check_f8_streaming_residual import H,exact_majorant


def sqrt_box(x,bits=80):
    x=Q(x); assert x>=0
    d=2**bits;n=isqrt((x*d*d).numerator//(x*d*d).denominator)
    return Q(n,d),Q(n+1,d)


def log_series(x,n=32):
    # 1<=x<=2; positive atanh series with geometric remainder.
    assert 1<=x<=2
    u=(x-1)/(x+1);s=sum(2*u**(2*j+1)/Q(2*j+1) for j in range(n))
    return s,s+2*u**(2*n+1)/((2*n+1)*(1-u*u))


def log_box(x):
    x=Q(x);assert x>=1
    m=0
    while x>2:x/=2;m+=1
    a,b=log_series(x);c,d=log_series(Q(2));return a+m*c,b+m*d


def clock_F(b):
    # F(1/b)=log((1+sqrt(1+b²))/b)-sqrt(1+b²).
    a,c=sqrt_box(1+b*b);l=log_box((1+a)/b)[0];u=log_box((1+c)/b)[1]
    return l-c,u-a


def clock_box(t0,t1,blo,bhi):
    """Certify b bracket for elapsed clock interval [t0,t1] from b(0)=1.
    Candidate bounds may come from floating inversion; acceptance is rational.
    """
    t0,t1,blo,bhi=map(Q,(t0,t1,blo,bhi));assert 0<blo<=bhi and t0<=t1
    a,c=clock_F(Q(1));assert clock_F(bhi)[1]-a<=t0
    assert clock_F(blo)[0]-c>=t1
    # v=-b/sqrt(1+b²), s=1/(1+b²), a=b/(1+b²)^2
    v=(-bhi/sqrt_box(1+bhi*bhi)[0],-blo/sqrt_box(1+blo*blo)[1])
    s=(1/(1+bhi*bhi),1/(1+blo*blo));a=(blo/(1+bhi*bhi)**2,bhi/(1+blo*blo)**2)
    return (blo,bhi),v,s,a


def coefficients(A,B,h,dy,j):
    d=np.empty((4,4),object)
    for i,X in enumerate((A,B)):
        for k in range(2):
            u,w,n,m=map(Q,X[:,j+k]);d[i,k]=u;d[i+2,k]=h*w;d[i,k+2]=dy*n;d[i+2,k+2]=h*dy*m
    hh=H.astype(int).astype(object);return hh@d@hh.T


def diff(c,axis,h):
    d=c.T if axis else c
    out=np.array([[Q(i)*v/h for v in d[i]] for i in range(1,len(d))],object)
    return out.T if axis else out


def bern3(c):
    # Degree elevation included by using the same denominator degree 3.
    return np.array([[sum(c[a,b]*Q(comb(i,a)*comb(j,b),comb(3,a)*comb(3,b)) for a in range(min(i+1,c.shape[0])) for b in range(min(j+1,c.shape[1]))) for j in range(4)] for i in range(4)],object)


def combine(terms):
    lo=np.full((4,4),Q(0),object);hi=lo.copy()
    for c,(a,b) in terms:
        assert a<=b
        p=bern3(c);l=p*a;u=p*b;lo+=np.minimum(l,u);hi+=np.maximum(l,u)
    return lo,hi


def hull(terms,wall=False):
    a,b=combine(terms)
    if wall:a,b=a[:,0],b[:,0]
    return min(a.flat),max(b.flat)


def magnitude(pair):return max(map(abs,pair))


def enclose(A,B,h,dy,k2,box,src=(Q(0),Q(0)),src_t=(Q(0),Q(0))):
    h,dy=Q(h),Q(dy);(bl,bh),v,s,a=box;v0,v1=v;s0,s1=s;a0,a1=a;k0,k1=k2
    assert min(h,dy,bl,k0)>0 and v1<0
    ss=Q(0)
    for j in range(A.shape[1]-1):
        c=coefficients(A,B,h,dy,j);ct,cy=diff(c,0,h),diff(c,1,dy);ctt,cty,cyy=diff(ct,0,h),diff(ct,1,dy),diff(cy,1,dy)
        zl,zh=bl+j*dy,bh+(j+1)*dy
        # r=-L V: combine SIGNED coefficients before taking absolute hull.
        r=hull([(ctt,(1,1)),(cty,(-2*v1,-2*v0)),(cyy,(-s1,-s0)),(cy,(3/zh-a1,3/zl-a0)),(c,k2)])
        ss+=dy*magnitude(r)**2/zl**3
        if j==0:
            one=np.array([[Q(1)]],object)
            g=hull([(one,src),(ct,(-v1,-v0)),(cy,(-s1,-s0))],True)
            gt=hull([(one,src_t),(ct,(-a1,-a0)),(ctt,(-v1,-v0)),(cy,(2*v0*a1,2*v1*a0)),(cty,(-s1,-s0))],True)
    return h*sqrt_box(ss)[1],h*magnitude(g),h*magnitude(gt)


def energy_step(B,h,kmax,box,bounds,d=Q(1,8)):
    """Upper bound on entire slab and terminal lifted-state energy norm.
    chi=(1-y/d)_+², top collar; homogeneous boundary energy E'<=5E.
    """
    h,kmax,B,d=map(Q,(h,kmax,B,d));(bl,bh),v,s,a=box
    vmin=-v[1];vmax=-v[0];assert vmin>0 and 0<5*h/2<1
    R,G,GT=bounds;A=G/vmin;At=GT/vmin+G*a[1]/vmin**2
    F=R+sqrt_box(d/bl**3)[1]*(kmax*A+At+(2*vmax+sqrt_box(s[1])[1])*2*A/d)
    return (B+F)/(1-5*h/2)


def check():
    import sympy as S
    x,y=S.symbols('x y');h=Q(1,4);dy=Q(1,2)
    checks=0
    # Pure cancellation in common degree: V_TT and k²V terms can oppose.
    p=np.array([[Q(1)],[Q(0)],[Q(-1,2)]],object)
    assert hull([(p,(1,1)),(p,(-1,-1))])==(0,0);checks+=1
    for n in range(4):
        for m in range(4):
            c=np.zeros((n+1,m+1),object);c[n,m]=Q(1);beta=bern3(c)
            poly=sum(beta[i,j]*comb(3,i)*comb(3,j)*x**i*(1-x)**(3-i)*y**j*(1-y)**(3-j) for i in range(4) for j in range(4))
            assert S.expand(poly-x**n*y**m)==0;checks+=1
    # Actual clock bracket, verified independently of float evaluation.
    b=clock_box(0,h,Q(3,4),Q(1000001,1000000));checks+=1
    try:clock_box(0,h,Q(99,100),Q(1000001,1000000))
    except AssertionError:checks+=1
    else:raise AssertionError('bad clock accepted')
    # Constant-clock manufactured wave V=T²+y³+Ty, bounds include signed wall.
    def jets(t):return np.array([[1+t*t+z**3+t*z for z in (Q(0),dy,2*dy)], [2*t+z for z in (Q(0),dy,2*dy)], [3*z*z+t for z in (Q(0),dy,2*dy)], [Q(1)]*3],object)
    A,B=jets(0),jets(h)
    # Use original moving coefficient interval, sample only as negative-control check.
    for k in (1,2,3):
        q=enclose(A,B,h,dy,(Q(k*k),Q(k*k)),b,(-h,h),(-1,1))
        old=exact_majorant(A,B,h,dy,k*k,(b[0][0],-b[1][0],b[2][1],b[3][1]),h,1)
        assert all(z>=0 for z in q) and q[0]<=old[0]+h*Q(1,2**40);checks+=1
        e=energy_step(0,h,k,b,q);assert e>=q[0];checks+=1
    return dict(checks=checks,scope='exact manufactured and rational clock/energy algebra; no original whole-trajectory certificate')

if __name__=='__main__':print(json.dumps(check(),indent=2))
