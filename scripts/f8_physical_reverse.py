"""Physical-only VJP for Weyl consumers; full signed forward state retained."""
import numpy as np
from ksw668_f8_signed_route_stage import defect
from warp_stage_adjoint import transpose


def rhs_physical_transpose(Y,dr,dy,b,v,route):
    if Y.ndim!=4 or Y.shape[:2]!=(3,3) or route not in ('paired','ledger'):
        raise ValueError('physical cotangent/route required')
    if np.any(Y[..., -1]):raise ValueError('cotangent outside active radial carrier')
    out=transpose(Y,dr,dy,b,v,4)
    if route=='paired':
        a,c=(1+v)/2,(1-v)/2
        B=(b+dy*np.arange(Y.shape[-2]))**-3;B[[0,-1]]*=.5;B=B[None,:,None]
        p=Y[1]+Y[2];q=(1-v)*Y[1]-(1+v)*Y[2]
        w=-B*defect(q/B,b,dy,True)
        n=(1-v*v)*(B*defect(p/B,b,dy))
        out[1]+=a*w+n/2;out[2]+=c*w-n/2
    out[..., -1]=0
    return out


def reverse_physical(Y,T,dt,coeff,dr,dy,route):
    def BT(y,t):
        v,b,_=coeff(t)
        return y+dt*rhs_physical_transpose(y,dr,dy,b,v,route)
    l2=2*BT(Y,T+dt/2)/3
    l1=BT(l2,T+dt)/4
    return Y/3+3*l2/4+BT(l1,T)


def physical_observation(o):
    if o.ndim!=4 or o.shape[:2]!=(6,3) or np.any(o[3:]) or np.any(o[..., -1]):
        raise ValueError('observer has nonphysical or inactive cotangent')
    return o[:3].copy()


def signed_contribution(lam,d):
    if lam.shape[0]!=3 or d.shape!=(6,*lam.shape[1:]):raise ValueError('carrier mismatch')
    out=np.zeros((6,3))
    out[:3]=np.sum(lam*d[:3],axis=(2,3))
    return out
