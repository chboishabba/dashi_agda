"""Frequency-adapted normal lift for the existing F8 characteristic energy.
Profile-only check, not full evolution or a proof by numerical sampling.
"""
import json
import numpy as np


def profiles(lam,dy,ny):
    lam=np.asarray(lam,float)
    if np.any(lam<0) or dy<=0 or ny<3:raise ValueError('lift geometry')
    alpha=np.sqrt(1+lam);y=np.arange(ny)*dy;Y=y[-1]
    return alpha,(1-y[:,None]/Y)*np.exp(-y[:,None]*alpha)


def derivative(f,dy):
    z=np.empty_like(f);z[0]=(f[1]-f[0])/dy;z[-1]=(f[-1]-f[-2])/dy
    z[1:-1]=(f[2:]-f[:-2])/(2*dy)
    return z


def check():
    maxima=np.zeros(4);count=0
    for t in (1.,2.,12.):
        for ny in (17,33,65,129,257):
            dy=2.016/(ny-1);z=1/t+np.arange(ny)*dy
            H=np.full(ny,dy);H[[0,-1]]*=.5
            B=H*z**-3
            lam=np.r_[0.,1.,(np.array([.01,.1,1.,4.])/dy)**2]
            alpha,chi=profiles(lam,dy,ny)
            assert np.all(chi[0]==1) and np.all(chi[-1]==0)
            D=derivative(chi,dy);Dw=z[:,None]**1.5*derivative(z[:,None]**-1.5*chi,dy)+1.5*chi/z[:,None]
            norm=lambda x:np.sum(B[:,None]*x*x,axis=0)
            # Remove the fixed time-dependent upper weight b^-3 for comparison.
            scaled=np.array([alpha*norm(chi),norm(D)/alpha,norm(Dw)/alpha,lam*norm(chi)/alpha])/t**3
            assert np.isfinite(scaled).all()
            maxima=np.maximum(maxima,scaled.max(axis=1));count+=len(lam)
    return dict(cases=count,max_scaled_profile_norms=maxima.tolist(),max_alpha_dy=float(np.sqrt(4**2+(2.016/16)**2)))


if __name__=='__main__':print(json.dumps(check(),indent=2))
