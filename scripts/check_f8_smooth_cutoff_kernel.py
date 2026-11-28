"""F8 auxiliary C2 positive bounded continuation, same exterior operator.
Reuse the parameter-polynomial residual consumer; no physical model change.
"""
import json,sys
from fractions import Fraction as Q
import numpy as np
from numba import njit
from check_f8_kernel_hermite_residual import I,D,U,rat,elevate
from check_f8_parameter_kernel import run,symbolic,mulz3,elevsrc
C=Q(15*13**2,4);cut=Q(1,13);width=cut/4;flat=C*Q(41,32)

@njit(cache=True)
def potential(z,k):
    if z>=1/13:return k*k+3.75/z**2
    t=min(1.,(1/13-z)*52)
    return k*k+(15*13**2/4)*(1+t*(.5+t*(.1875+t*(-.75+t*.34375))))

@njit(cache=True)
def grid(xi,k,h,na,nb):
    # Same characteristic trapezoid recurrence; only auxiliary V changed.
    r=np.ones((na+1,nb+1));d=h*h/16
    for i in range(1,na+1):
        for j in range(1,nb+1):
            q=d*potential(xi+(i-j)*h/2,k);a=r[i-1,j];b=r[i,j-1];c=r[i-1,j-1];r[i,j]=((1-q)*(a+b)-(1+q)*c)/(1+q)
    return r

@njit(cache=True)
def derivatives(r,xi,k,h):
    a=np.zeros_like(r);b=np.zeros_like(r)
    for i in range(r.shape[0]):
        for j in range(r.shape[1]):
            q=potential(xi+(i-j)*h/2,k)*r[i,j]
            if j:a[i,j]=a[i,j-1]-h*(q+potential(xi+(i-j+1)*h/2,k)*r[i,j-1])/8
            if i:b[i,j]=b[i-1,j]-h*(q+potential(xi+(i-j-1)*h/2,k)*r[i-1,j])/8
    return a,b

def candidate(xi,k,h,na,nb):
    r=grid(xi,k,h,na,nb);a,b=derivatives(r,xi,k,h);f=grid(xi,k,h/2,2*na,2*nb);fa,fb=derivatives(f,xi,k,h/2)
    r,a,b=[(4*f0[::2,::2]-c)/3 for f0,c in ((f,r),(fa,a),(fb,b))]
    z=xi+(np.arange(na+1)[:,None]-np.arange(nb+1)[None,:])*h/2;t=np.clip((1/13-z)*52,0,1);v=k*k+np.where(z>=1/13,3.75/np.maximum(z,1/13)**2,float(C)*(1+t*(.5+t*(.1875+t*(-.75+t*.34375)))))
    assert np.all(r[0]==1) and np.all(r[:,0]==1) and not np.any(a[:,0]) and not np.any(b[0])
    return r,a,b,-v*r/4

def elevall(p):return elevsrc(elevate(elevate(p,0),1))
def envelope(p,q,z,h,w,zl,zh,k2,physical):
    c=rat(cut);d=rat(width);left=rat(cut-width);den=np.maximum(c.l,zl)
    bound=np.maximum(physical,np.where(zl<=left.h,np.max((q+rat(flat)*p).mag(),axis=(0,1,2)),0))
    mask=(zl<=c.h)&(zh>=left.l)
    if np.any(mask):
        P=p[:,:,:,mask];Q0=q[:,:,:,mask];Z=z[mask];base=P;v=rat(Q(11,32))*P
        for a in (Q(-3,4),Q(3,16),Q(1,2),Q(1)):
            base=elevall(base);Q0=elevall(Q0);v=(c*elevall(v)-mulz3(v,Z,h,w))/d+rat(a)*base
        bound[mask]=np.maximum(bound[mask],np.max((Q0+rat(C)*v).mag(),axis=(0,1,2)))
    V=np.where(zl<=c.h,U(k2.h+rat(flat).h),U(k2.h+U(3.75/D(den*den))))
    return bound,V

def exact():
    import sympy as S
    t,z=S.symbols('t z');p=1+t/2+3*t*t/16-3*t**3/4+11*t**4/32;ref=(1-t/4)**-2
    checks=[]
    for j in range(3):assert S.diff(p,t,j).subs(t,0)==S.diff(ref,t,j).subs(t,0);checks.append('physical join order '+str(j))
    assert p.subs(t,1)==S.Rational(41,32);checks.append('plateau value')
    for j in (1,2):assert S.diff(p,t,j).subs(t,1)==0;checks.append('flat join order '+str(j))
    assert S.factor(S.diff(p,t)-(1-t)**2*(11*t+4)/8)==0;checks.append('monotone derivative factor')
    assert 0<cut-width<cut<Q(1,12);checks.append('extension outside original wall')
    return checks
if __name__=='__main__':
    out=run(int(sys.argv[1]),int(sys.argv[2]),int(sys.argv[3]),2.**-int(sys.argv[4]),int(sys.argv[5]),sys.modules[__name__]);print(json.dumps(dict(symbolic_checks=symbolic(),extension_checks=exact(),extension='C2 positive quartic, same exterior',**out)),flush=True)
