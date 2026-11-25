"""Original F8 fixed-window signed interval parametrix; exact dyadic arithmetic.
Local slab reference, not an all-clock or physical certificate.
"""
from fractions import Fraction as Q
from math import factorial, isqrt, comb
import json
from functools import lru_cache
from check_f8_combined_residual import clock_F, clock_box, coefficients, diff, hull, magnitude, energy_step
import numpy as np

S=2**80
class I:
    __slots__=('l','h')
    def __init__(self,l=0,h=None):
        if isinstance(l,I):self.l,self.h=l.l,l.h;return
        l=Q(l);h=l if h is None else Q(h);assert l<=h
        self.l=Q(l*S//1,S);self.h=Q(-((-h*S)//1),S)
    def __add__(a,b):
        b=I(b);return I(a.l+b.l,a.h+b.h)
    __radd__=__add__
    def __neg__(a):return I(-a.h,-a.l)
    def __sub__(a,b):return a+-I(b)
    def __rsub__(a,b):return I(b)+-a
    def __mul__(a,b):
        b=I(b);p=[x*y for x in (a.l,a.h) for y in (b.l,b.h)];return I(min(p),max(p))
    __rmul__=__mul__
    def __truediv__(a,b):
        b=I(b);assert b.l*b.h>0,'division interval contains zero';return a*I(1/b.h,1/b.l)
    def __rtruediv__(a,b):return I(b)/a
    def __pow__(a,n):
        if n<0:return (1/a)**(-n)
        if n==0:return I(1)
        if n%2==0:
            lo=0 if a.l<=0<=a.h else min(a.l*a.l,a.h*a.h)
            return I(lo,max(a.l*a.l,a.h*a.h))**(n//2) if n!=2 else I(lo,max(a.l*a.l,a.h*a.h))
        return a*(a**(n-1))
    def mag(a):return max(abs(a.l),abs(a.h))
    def sqrt(a):
        assert a.l>=0
        return I(Q(isqrt((a.l*S*S)//1),S),Q(isqrt((a.h*S*S)//1)+1,S))
    def floats(a):return [float(a.l),float(a.h)]
    def contains(a,b):return a.l<=b<=a.h

def expneg(x):
    """exp(-x), x>=0. Alternating series on [0,1], then squaring."""
    x=I(x);assert x.l>=0
    def point(t):
        if t>=80:return I(0,Q(1,S)) # e>2
        m=0
        while t>1:t/=2;m+=1
        v=sum((-t)**j/factorial(j) for j in range(24));w=v+t**24/factorial(24)
        z=I(v,w)
        for _ in range(m):z=z*z
        return z
    return I(point(x.h).l,point(x.l).h)

@lru_cache(None)
def normalizer():
    # bump even and monotone on [0,1]; endpoint rectangle sums, exact width .1.
    n=128;f=[expneg(I(1/(1-Q(j,n)**2)-1)) for j in range(n)]+[I(0)]
    return I(sum(x.l for x in f[1:])/ (5*n),sum(x.h for x in f[:-1])/(5*n))

# Normalized time jets. Every truncation retains requested lower derivatives.
def const(x,n):return [I(x)]+[I() for _ in range(n-1)]
def add(a,b):return [x+y for x,y in zip(a,b)]
def neg(a):return [-x for x in a]
def mul(a,b):return [sum((a[i]*b[j-i] for i in range(j+1)),I()) for j in range(len(a))]
def scale(a,x):return [v*x for v in a]
def der(a):return [a[j+1]*(j+1) for j in range(len(a)-1)]+[I()]
def inv(a):
    b=[1/a[0]]
    for j in range(1,len(a)):b.append(-sum((a[i]*b[j-i] for i in range(1,j+1)),I())/a[0])
    return b
def sqrtj(a):
    b=[a[0].sqrt()]
    for j in range(1,len(a)):b.append((a[j]-sum((b[i]*b[j-i] for i in range(1,j)),I()))/(2*b[0]))
    return b

def bjets(b,n):
    B=const(b,n)
    for j in range(n-1):
        v=neg(mul(B,inv(sqrtj(add(const(1,n),mul(B,B))))))
        B[j+1]=v[j]/(j+1)
    return B

@lru_cache(None)
def bump_polys(n):
    # f^(j)=u^parity P_j(z) exp(1-z), z=1/(1-u²).
    import sympy as s
    z=s.symbols('z');p=s.Integer(1);odd=0;out=[]
    for j in range(n):
        out.append((odd,tuple(int(p.coeff(z,i)) for i in range(s.degree(p,z)+1))))
        p=s.expand(p+2*(z*z-z)*(s.diff(p,z)-p) if odd else 2*z*z*(s.diff(p,z)-p));odd=1-odd
    return out

def bump(u,n,rate=10,normalize=True):
    if u.h<=-1 or u.l>=1:return const(0,n)
    # An interval touching a flat endpoint uses monomial exponential maxima;
    # it must not evaluate 1/(1-u²) across its pole.
    lo=max(Q(-1),u.l);hi=min(Q(1),u.h);abslo=0 if lo<=0<=hi else min(abs(lo),abs(hi));abshi=max(abs(lo),abs(hi))
    zl=1/(1-abslo**2);out=[]
    for j,(odd,p) in enumerate(bump_polys(n)):
        if abshi<1 and zl<80:
            z=I(zl,1/(1-abshi**2));v=I()
            # Avoid huge powers times tiny exponential near flat endpoints.
            if z.h<=80:
                for a in reversed(p):v=v*z+a
                v=v*expneg(z-1)*(I(lo,hi) if odd else 1)
            else:v=None
        else:v=None
        if v is None:
            bound=Q(0)
            for i,a in enumerate(p):
                if not a:continue
                z=max(zl,Q(i),Q(1))
                # For large z, avoid a fixed absolute exp rounding times z^i:
                # use z>=80 and z^i e^(1-z) decreasing for z>=i; evaluate at min(z,80) if i<=80.
                if z>80 and i<=80:z=Q(80)
                bound+=abs(a)*z**i*expneg(I(z-1)).h
            v=I(-bound,bound)
        out.append(v*Q(rate**j,factorial(j))/(normalizer() if normalize else 1))
    return out

# polynomial in Z, coefficients time jets
def padd(a,b,n):return [add(a[i] if i<len(a) else const(0,n),b[i] if i<len(b) else const(0,n)) for i in range(max(len(a),len(b)))]
def pmul(a,b):return [mul(x,b) for x in a]
def pscale(a,x):return [scale(v,x) for v in a]
def shift(a,j,n):return [const(0,n) for _ in range(j)]+a

def dual(box,u,k,m,receiver, audit=False):
    assert 0<=m<=8 and k.l>0 and receiver in (0,1)
    n=m+6;b=bjets(I(*box[0]),n);b2=mul(b,b);beta=sqrtj(add(const(1,n),b2));ib=inv(b);ibeta=inv(beta);s=mul(ibeta,ibeta);v=neg(mul(b,ibeta));a=der(v)
    chi=bump(u,n);scale0,extra,sign=((Q(1,4),0,-1),(Q(1,2),2,1))[receiver]
    a2=scale(mul(mul(b2,mul(beta,beta)),chi),-scale0)
    J=neg(mul(b2,ibeta));a1=scale(mul(mul(b2,add(J,scale(beta,extra))),chi),-scale0)
    a0=scale(mul(b2,chi),sign*scale0)
    q=add(add(der(der(a2)),neg(der(a1))),scale(a0,-(k*k)))
    qflux=mul(mul(b,b2),q)
    dz=lambda p:padd([scale(p[j],j) for j in range(1,len(p))],pscale(pmul(p,beta),-1),n)
    dt=lambda p:padd([der(c) for c in p],shift(pscale(pmul(p,der(beta)),-1),1,n),n)
    A=lambda p:padd(pmul(dt(dz(p)),scale(v,2)),pmul(dz(p),add(a,scale(ib,-3))),n)
    B=lambda p:pscale(dt(dt(p)),-1)
    def warp(p,l,remainder=False):
        factor=const(-3*((-1)**l),n)
        for _ in range(l+(0 if remainder else 1)):factor=mul(factor,ib)
        if remainder:factor=scale(factor,I(0,ib[0].h)) # 1/(b+y), only value used
        return shift(pmul(dz(p),factor),l,n)
    def solve(rhs,flux):
        p=[const(0,n) for _ in range(len(rhs)+2)]
        for i in reversed(range(len(rhs))):
            p[i+1]=add(scale(mul(p[i+2],ibeta),Q(i+2,2)),scale(mul(rhs[i],beta),-Q(1,2*(i+1))))
        p[0]=add(mul(p[1],ibeta),neg(mul(flux,beta)))
        return p[:-1]
    p=[[neg(mul(beta,qflux))]]
    for j in range(m):
        rhs=A(p[j]);rhs=padd(rhs,B(p[j-1]),n) if j else rhs
        for l in range(1,j+1):rhs=padd(rhs,warp(p[j-l],l),n)
        p.append(solve(pscale(rhs,-1),neg(mul(v,der(p[j][0])))))
    pc=[const(0,n),neg(mul(mul(v,mul(beta,beta)),der(p[m][0])))]
    # Exact cancellation of the lower orders. Combine surviving signed terms.
    residual=pscale(A(p[m]),k**(-m));residual=padd(residual,pscale(B(p[m]),k**(-m-1)),n)
    if m:residual=padd(residual,pscale(B(p[m-1]),k**(-m)),n)
    for j in range(m+1):
        l=max(1,m-j);residual=padd(residual,pscale(warp(p[j],l,True),k**(-j-l)),n)
    residual=padd(residual,[scale(mul(pc[1],ibeta),-2*k**(-m))],n)
    residual=padd(residual,pscale(A(pc),k**(-m-1)),n);residual=padd(residual,pscale(B(pc),k**(-m-2)),n)
    residual=padd(residual,pscale(warp(pc,1,True),k**(-m-2)),n)
    poly=[const(0,n)]
    for j,P in enumerate(p):poly=padd(poly,pscale(P,k**(-j-1)),n)
    poly=padd(poly,pscale(pc,k**(-m-2)),n)
    # beta>=1; integral Z^(2l) exp(-2Z) <= (l!)², dy=dZ/k.
    norm=(I(box[0][0])**(-3)/k).sqrt()*sum(c[0].mag()*factorial(j) for j,c in enumerate(residual))
    if audit:
        d=add(mul(v,der(poly[0])),scale(mul(s,dz(poly)[0]),k))[0]-qflux[0]
        assert d.contains(0), 'wall flux identity not enclosed'
        # Compare independent direct operator evaluation with cancelled remainder.
        # Interval overlap is a regression, not a proof of the recurrence.
        for Z in (I(0),I(1),I(3)):
            def ev(p):
                x=I()
                for c in reversed(p):x=x*Z+c[0]
                return x
            ds=pscale(padd([scale(poly[j],j*(j-1)) for j in range(2,len(poly))],pscale(pmul([scale(poly[j],j) for j in range(1,len(poly))],beta),-2),n),k*k)
            direct=ev(pmul(ds,s))+k*ev(A(poly))+ev(B(poly))+k*(3*ib[0]-3/(b[0]+Z/k))*ev(dz(poly))
            cancelled=ev(residual)
            assert max(direct.l,cancelled.l)<=min(direct.h,cancelled.h), 'direct/remainder disagreement'
    return [c[0] for c in poly], beta[0], norm.h, q[0]

def phi_range(poly,beta,k,y):
    Z=k*y;p=I()
    for c in reversed(poly):p=p*Z+c
    return p*expneg(beta*Z)

def pairing(A,B,h,dy,k,box,poly,beta,src=I(0)):
    """Signed interval integrals over a slab; no quadrature samples."""
    h,dy=Q(h),Q(dy);(bl,bh),v,s,a=box;V,S,Aa=I(*v),I(*s),I(*a);bulk=I();wall=I()
    for j in range(A.shape[1]-1):
        c=coefficients(A,B,h,dy,j);ct,cy=diff(c,0,h),diff(c,1,dy);ctt,cty,cyy=diff(ct,0,h),diff(ct,1,dy),diff(cy,1,dy)
        y=I(j*dy,(j+1)*dy);z=I(bl,bh)+y;w=z**(-3);p=phi_range(poly,beta,k,y)
        C=3/z-Aa;K=k*k
        r=I(*hull([(ctt,(1,1)),(cty,(-2*V.h,-2*V.l)),(cyy,(-S.h,-S.l)),(cy,(C.l,C.h)),(c,(K.l,K.h))]))
        bulk+=h*dy*w*p*r
        if j==0:
            g=I(*hull([(np.array([[Q(1)]],object),(src.l,src.h)),(ct,(-V.h,-V.l)),(cy,(-S.h,-S.l))],True))
            wall=h*I(bl,bh)**(-3)*poly[0]*g
    return bulk,wall

def ceil_dyadic(x,bits=80):
    d=2**bits;return Q(-((-Q(x)*d)//1),d)

def slab_weld(incoming,h,dy,k,box,primal_bounds,A,B,u,m,receiver,src=I(0)):
    # Includes entire-slab bound; no reset of incoming energy. A single m
    # must be fixed across the window, or temporal Green jumps charged.
    Bplus=ceil_dyadic(energy_step(incoming,h,k.h,box,primal_bounds))
    poly,beta,D,q=dual(box,u,k,m,receiver)
    bulk,wall=pairing(A,B,h,dy,k,box,poly,beta,src)
    radius=ceil_dyadic(Bplus*Q(h)*D/k.l)
    return Bplus,bulk,wall,radius,D,q

@lru_cache(None)
def exact_span():
    a,c=clock_F(Q(1));l,h=clock_F(Q(1,12));return I(l-c,h-a)

def window_coordinate(t0,t1):
    return 10*(I(t0,t1)-exact_span()+Q(3,20))

@lru_cache(None)
def source_coeff(n):
    # Exact low-mode source coefficient: interval rectangle integration,
    # same original compact emitter; no 256/512 convergence assumption.
    k=I(Q(n)*Q(333,106)/Q('3.012'),Q(n)*Q(355,113)/Q('3.012'));eps=Q(1,25)
    assert (k*eps).h<=1
    N=256;total=I()
    def sin(x):
        # alternating Taylor, monotone on [0,1]
        def s(t,m):return sum((-1)**j*t**(2*j+1)/factorial(2*j+1) for j in range(m))
        return I(s(x.l,4),s(x.h,5))
    for j in range(N):
        u=I(Q(j,N),Q(j+1,N));f=bump(u,1,normalize=False)[0]
        total+=u*sin(k*eps*u)*f/N
    return I(Q(2)/Q('3.012')).sqrt()*eps**6*total

def source_box(box,t0,t1,n):
    u=I(t0,t1)*Q(400,13)-1
    if u.h<=-1 or u.l>=1:return I(),I()
    b=bjets(I(*box[0]),2);amp=scale(inv(mul(b,sqrtj(add(const(1,2),mul(b,b))))),-6)
    x=mul(amp,bump(u,2,Q(400,13),False));c=source_coeff(n)
    return x[0]*c,x[1]*c
def check():
    import mpmath as mp
    mp.mp.dps=70;checks=0
    for x in (Q(0),Q(1,3),Q(1),Q(9),Q(79),Q(100)):
        v=expneg(I(x));f=mp.exp(-mp.mpf(x.numerator)/x.denominator)
        assert mp.mpf(v.l.numerator)/v.l.denominator<=f<=mp.mpf(v.h.numerator)/v.h.denominator;checks+=1
    z=normalizer();f=mp.mpf('0.1')*mp.quad(lambda u:mp.exp(1-1/(1-u*u)),[-1,0,1]);assert float(z.l)<=f<=float(z.h);checks+=1
    for j in (1,2):
        c=source_coeff(j);k=mp.pi*j/mp.mpf('3.012');e=mp.mpf('.04');f=mp.sqrt(2/mp.mpf('3.012'))*e**6*mp.quad(lambda u:u*mp.sin(k*e*u)*mp.exp(1-1/(1-u*u)),[0,1]);assert float(c.l)<=f<=float(c.h);checks+=1
    # Actual window location, elapsed times certified by rational clock comparisons.
    from math import floor,ceil
    from run_f8_streaming_residual import clock,T0,span
    h=Q(span/4516);i=4300;t0=i*h;t1=(i+1)*h
    b0,b1=clock(T0+float(t0))[0],clock(T0+float(t1))[0]
    box=clock_box(t0,t1,Q(floor(b1*10**10)-2,10**10),Q(ceil(b0*10**10)+2,10**10))
    u=window_coordinate(t0,t1);assert -1<u.l<=u.h<1;checks+=1
    rows=[]
    for n in (1,2,128,1024):
        k=I(Q(n)*Q(333,106)/Q('3.012'),Q(n)*Q(355,113)/Q('3.012'))
        for j in (0,1):
            vals=[]
            for m in range(5):
                _,_,r,_=dual(box,u,k,m,j,audit=True);vals.append(float(r));checks+=4
            rows.append(dict(n=n,receiver=j,orders=vals,best_order=min(range(5),key=vals.__getitem__)))
    # Flat window endpoints, source-free interval, and no reset of incoming energy.
    for q in (I(-2,-1),I(1,2)):
        assert all(v.l==v.h==0 for v in bump(q,8));checks+=1
    b=source_box(box,t0,t1,1);assert all(v.l==v.h==0 for v in b);checks+=1
    return dict(checks=checks,window_normalizer=z.floats(),window_u=u.floats(),source_coefficients=[source_coeff(j).floats() for j in (1,2)],dual_rows=rows,scope='local interval reference, direct operator overlap regressions, not full-clock receiver certificate')

if __name__=='__main__':print(json.dumps(check(),indent=2))
