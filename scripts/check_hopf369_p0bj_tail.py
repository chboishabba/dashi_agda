"""Exact BJ boundary limit and rational certificate for fitted BG tail.
The interval proof covers |x|=1, not the finite-radius compact interior.
"""
from fractions import Fraction as Q
from pathlib import Path
import json,sys
import sympy as s

SCALE=10**15

def floor(x):return Q((x*SCALE).__floor__(),SCALE)
def ceil(x):return Q((x*SCALE).__ceil__(),SCALE)
class I:
    def __init__(self,a,b=None):self.a=floor(Q(a));self.b=ceil(Q(a if b is None else b))
    @staticmethod
    def coerce(x):return x if isinstance(x,I) else I(x)
    def __add__(self,x):x=I.coerce(x);return I(self.a+x.a,self.b+x.b)
    __radd__=__add__
    def __neg__(self):return I(-self.b,-self.a)
    def __sub__(self,x):return self+-I.coerce(x)
    def __rsub__(self,x):return I.coerce(x)+-self
    def __mul__(self,x):
        x=I.coerce(x);z=[self.a*x.a,self.a*x.b,self.b*x.a,self.b*x.b];return I(min(z),max(z))
    __rmul__=__mul__
    def __truediv__(self,x):
        x=I.coerce(x);assert x.a*x.b>0
        return self*I(1/x.b,1/x.a)
    def __rtruediv__(self,x):return I.coerce(x)/self
    def __pow__(self,n):
        r=I(1)
        for _ in range(n):r=r*self
        return r
    def absmax(self):return max(abs(self.a),abs(self.b))

def atan_inv(n,N=20):
    x=Q(1,n);v=sum((-1)**k*x**(2*k+1)/(2*k+1) for k in range(N));w=v+(-1)**N*x**(2*N+1)/(2*N+1)
    return I(min(v,w),max(v,w))
PI=16*atan_inv(5)-4*atan_inv(239) # Machin's identity; alternating error.
N=20;x=Q(1,3);v=4*sum(x**(2*k+1)/(2*k+1) for k in range(N))
L=I(v,v+4*x**(2*N+1)/((2*N+1)*(1-x*x))) # 2 log 2.

def trig(k,z):
    # nearest quarter turn at interval midpoint; reduce to |arg|<1.
    mid=(z.a+z.b)/2; quadrant=round(4*k*mid)
    a=PI*(2*k*z-Q(quadrant,2));assert a.absmax()<1
    from math import factorial
    sn=sum((-1)**i*(a**(2*i+1))/factorial(2*i+1) for i in range(9))+I(-Q(1,factorial(19)),Q(1,factorial(19)))
    cs=sum((-1)**i*(a**(2*i))/factorial(2*i) for i in range(10))+I(-Q(1,factorial(20)),Q(1,factorial(20)))
    return ((cs,sn),(-sn,cs),(-cs,-sn),(sn,-cs))[quadrant%4]

def hyperbolic(z):
    from math import factorial
    a=L*(z-Q(1,2));assert a.absmax()<1
    # all omitted terms bounded by twice first omitted term at |a|<=1.
    cs=sum((a**(2*i))/factorial(2*i) for i in range(10))+I(-Q(2,factorial(20)),Q(2,factorial(20)))
    sn=sum((a**(2*i+1))/factorial(2*i+1) for i in range(9))+I(-Q(2,factorial(19)),Q(2,factorial(19)))
    return Q(4,5)*cs,sn/cs

def poly(co,z):
    a=I(0)
    for c in reversed(co):a=a*z+c
    return a

def deriv(co):return [k*co[k] for k in range(1,len(co))]

def exact_tail():
    n=4;y,h,j,beta=s.symbols('y h j beta',real=True); b=s.Function('b')(y); q=s.Function('q')(y); f=s.Function('f')(y)
    x=s.Matrix([1,0,0]); G=s.MutableDenseNDimArray.zeros(n,n,n); eye=s.eye(3)
    # Rotational covariance aligns unit x with e1; beta=eps*h*4*x3/F is a scalar on each fixed boundary direction.
    for k in range(3):
        for i in range(3):
            for l in range(3):G[k,i,l]=h*(x[l]*eye[k,i]-x[k]*eye[i,l])
    for i in range(3):
        G[3,i,i]=-b*s.diff(b,y);G[i,i,3]=G[i,3,i]=s.diff(b,y)/b
    base=s.diag(b*b,b*b,b*b,1);inv=base.inv();ell=[-h,0,0,0];E=-2*q*base
    for i in range(3):
        E[i,3]=E[3,i]=beta*x[i]
        for k in range(3):E[i,k]+=f*j*h*beta*(eye[i,k]-3*x[i]*x[k])
    U=s.MutableDenseNDimArray.zeros(n,n,n)
    for i in range(n):
        for k in range(n):
            for l in range(n):U[i,k,l]=s.expand((s.diff(E[k,l],y) if i==3 else 0)-sum(G[m,i,k]*E[m,l]+G[m,i,l]*E[k,m] for m in range(n))+2*ell[i]*E[k,l])
    C=s.MutableDenseNDimArray.zeros(n,n,n)
    for a in range(n):
        for i in range(n):
            for k in range(n):C[a,i,k]=s.expand(sum(inv[a,l]*(U[i,k,l]+U[k,i,l]-U[l,i,k])/2 for l in range(n)))
    def dc(a,i,k,l):return (s.diff(C[a,i,k],y) if l==3 else 0)+sum(G[a,l,m]*C[m,i,k]-G[m,l,i]*C[a,m,k]-G[m,l,k]*C[a,i,m] for m in range(n))
    R=s.Matrix(n,n,lambda i,k:s.expand(sum(dc(a,i,k,a)-dc(a,i,a,k)+2*(ell[a]*C[a,i,k]-ell[k]*C[a,i,a]) for a in range(n))))
    ans=s.simplify(3*s.trace(inv*E)+s.trace(inv*R));assert s.simplify(ans-(6*s.diff(q,y,2)+18*s.diff(b,y)*s.diff(q,y)/b-24*q))==0
    print('PASS exact boundary source cancellation with arbitrary beta, f(y), q(y), b(y)',flush=True)

def certify(c,N=256):
    # At r^2=1, radial argument is 10/11 and outer denominator 11.
    a=[[sum(Q(float(c[(i*4+k)*5+l]))*Q(10,11)**k for k in range(4))/11 for l in range(5)] for i in range(9)]
    d=[[sum(Q(float(c[180+(i*4+k)*2+l]))*Q(10,11)**k for k in range(4))/11 for l in range(2)] for i in range(9)]
    angular=[1,1,1,1,Q(1,2),Q(1,2),Q(1,2),1,2]
    p=[[0,0,Q(1,2),-Q(3,2),Q(3,2),-Q(1,2)],[0,0,0,Q(1,2),-1,Q(1,2)]]
    mx=Q(0)
    for k in range(N):
        z=I(Q(k,N),Q(k+1,N));b,tanh=hyperbolic(z);omega=2*PI/L
        C1,S1=trig(1,z);C2,S2=trig(2,z)
        Y=[I(1),C1,S1,C2,S2];DY=[I(0),-omega*S1,omega*C1,-2*omega*S2,2*omega*C2];DDY=[I(0),-omega**2*C1,-omega**2*S1,-4*omega**2*C2,-4*omega**2*S2]
        pv=[L**2*poly(q,z) for q in p];dp=[L*poly(deriv(q),z) for q in p];ddp=[poly(deriv(deriv(q)),z) for q in p]
        B=Q(0)
        for i in range(9):
            P=sum(x*y for x,y in zip(a[i],Y));P1=sum(x*y for x,y in zip(a[i],DY));P2=sum(x*y for x,y in zip(a[i],DDY))
            Q0=sum(x*y for x,y in zip(d[i],pv));Q1=sum(x*y for x,y in zip(d[i],dp));Q2=sum(x*y for x,y in zip(d[i],ddp))
            F=-18*Q(16,25)/(b**2)*P+30*tanh*P1+6*P2+6/b*(Q2+3*tanh*Q1-4*Q0)
            B+=angular[i]*F.absmax()
        mx=max(mx,B)
    # Reference boundary derivative is -18*h0^2/b^2 <= -11.52.
    print('uniform rational boundary weighted residual bound',float(mx),'intervals',N,flush=True)
    assert mx<Q(288,625) # .04 * 11.52 = .4608
    print('certified boundary barrier margin >=',float(Q(288,625)-mx),flush=True)

if __name__=='__main__':
    exact_tail(); c=json.loads(Path(sys.argv[1]).read_text().split('COEFFICIENTS ')[-1]);assert len(c)==252
    certify(c)
