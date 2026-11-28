"""Exact binary-input affine population event residual enclosure.
This is a fixed recorded material history, not a validated real reaction path.
"""
from fractions import Fraction as F
from math import isqrt
import numpy as np


def q(v):
    return v if isinstance(v,F) else F(v) if isinstance(v,(int,str)) else F(float(v))


def sqrt_interval(x,bits=80):
    """Dyadic enclosure, relative scaling even for very small binary inputs."""
    x=q(x)
    if x<0 or bits<2:raise ValueError('invalid square root chart')
    if x==0:return F(0),F(0)
    shift=bits-(x.numerator.bit_length()-x.denominator.bit_length())//2
    scale=F(2)**shift;z=x*scale*scale
    k=isqrt(z.numerator//z.denominator);lo=F(k)/scale
    hi=lo if lo*lo==x else F(k+1)/scale
    assert lo*lo<=x<=hi*hi
    return lo,hi


def scaled(iv,v):
    a,b=(iv[0]*v,iv[1]*v);return min(a,b),max(a,b)


def event_rounding_receipt(z,n,r,a,b,V,mass,charge,out,bits=80):
    """Exact enclosure of rounded output minus exact affine binary event.
    Treat all supplied binary event inputs, including density/rates, as fixed.
    Nonexpansiveness follows from remain^2 <= old*new on each species.
    """
    z,b,out=[np.asarray(v,float).reshape(-1,3) for v in (z,b,out)]
    n,r,a,mass,charge=map(lambda v:np.asarray(v,float),(n,r,a,mass,charge))
    if n.ndim!=1 or any(v.shape!=n.shape for v in (r,a,mass,charge)) or z.shape!=b.shape or z.shape!=out.shape or len(z)!=len(n):raise ValueError('invalid event chart')
    if not all(np.isfinite(v).all() for v in (z,b,out,n,r,a,mass,charge)) or not np.isfinite(V) or V<=0 or np.any(mass<=0) or np.any(charge==0):raise ValueError('invalid event data')
    total=F(0);radii=[];intervals=[]
    for j in range(len(n)):
        N,R,A=map(q,(n[j],r[j],a[j]));remain=N-R;new=remain+A
        if min(N,R,A,remain)<0:raise ValueError('negative event density')
        if N==0 and np.any(z[j]!=0):raise ValueError('uninhabited input current')
        if remain*remain>N*new:raise ArithmeticError('event not contractive')
        coef=sqrt_interval(remain*remain/(N*new),bits) if N*new else (F(0),F(0))
        shift=sqrt_interval(A*A*q(V)*q(mass[j])/new,bits) if new else (F(0),F(0))
        for k in range(3):
            l,u=scaled(coef,q(z[j,k]));v,w=scaled(shift,q(b[j,k])*(1 if charge[j]>0 else -1))
            l+=v;u+=w;actual=q(out[j,k]);err=max(abs(actual-l),abs(actual-u));total+=err
            radii.append(str(err));intervals.append([str(l),str(u)])
    return dict(error_l1_exact=str(total),component_error_exact=radii,output_intervals_exact=intervals,
        fixed_binary_material_history=True,physical_coefficient_rounding_admitted=False)
