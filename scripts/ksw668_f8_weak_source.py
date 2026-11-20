"""Opt-in r^2 weak source representative; original FV emitter unchanged."""
import numpy as np
from scipy.special import roots_legendre


def weak_source(eps, rgrid, dr, nodes=256):
    r = np.asarray(rgrid, dtype=float)
    if eps <= 0 or dr <= 0 or len(r) < 3 or not np.allclose(r, np.arange(len(r))*dr, rtol=1e-13, atol=1e-15):
        raise ValueError('uniform radial grid from origin required')
    if r[-2] < eps or nodes < 32:
        raise ValueError('source must fit before enforced outer node; sufficient quadrature required')
    u=r/eps; h=dr/eps
    x,w=roots_legendre(nodes); x=(x+1)/2; w=w/2
    out=np.zeros((3,len(r)))
    # Original normalized TT differential profiles with common bump factored
    # BEFORE floating evaluation; avoids cancellation at the radial origin.
    polys=([6,81,-92,-46,70,-15],[6,54,-109,58,-7],[24,-36,12,1])
    scale=(8/5,32/7,16/35)
    for q,ell in enumerate((0,2,4)):
        d=3+2*ell; load=np.zeros(len(r))
        for j,(a,b) in enumerate(zip(u[:-1],u[1:])):
            c=min(b,1.)
            if a>=c: break
            z=a+(c-a)*x; zz=z*z; gap=(1-z)*(1+z)
            profile=scale[q]*np.polyval(polys[q],zz)*np.exp(1-1/gap-8*np.log(gap))
            right=(zz-a*a)/(b*b-a*a)
            mass=(c-a)*w*z**(d-1)*profile
            load[j]+=mass@(1-right); load[j+1]+=mass@right
        W=((u+h/2)**d-np.maximum(0.,u-h/2)**d)/d
        out[q]=load/W
    if not np.isfinite(out).all() or np.any(out[:,-1]): raise ValueError('invalid weak source')
    return out
