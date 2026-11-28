"""Local comparison with original weighted4 six-channel stage."""
import math,time,json
import numpy as np
from scipy.optimize import brentq
from ksw668_f8_tt_multipole import F
from ksw668_f8_signed_route_stage import step
from f8_fused_step import step_into

def setup(dr,nr):
    j=np.arange(1,nr,dtype=float);cp=np.zeros((3,nr));cm=cp.copy()
    for q,d in enumerate((3,7,11)):
        den=(j+.5)**d-(j-.5)**d;cp[q,1:]=d*(j+.5)**(d-1)/den;cm[q,1:]=d*(j-.5)**(d-1)/den
    return cp,cm

def check():
    rng=np.random.default_rng(1547);rows=[];h=.0005999023910881472
    for dr,dy,nr,ny in ((.008,.012,13,5),(.008,.012,378,337),(.006,.009,503,449)):
        cp,cm=setup(dr,nr);src=rng.normal(size=(3,nr));src[:,-1]=0
        for route in ('ledger','paired'):
            for t in (1.,2.,12.):
                X=rng.normal(size=(6,3,ny,nr));X[..., -1]=0;X[4,:,1:]=0;X[5,:,:-1]=0
                def coeff(T):
                    u=brentq(lambda u:F(u)-T,.5,25);return -1/math.sqrt(1+u*u),1/u,.23
                a,b,out=[np.empty_like(X) for _ in range(3)];T=F(t)
                Y=step(X,T,h,coeff,dr,dy,src,cp,cm,route)
                start=time.monotonic();Z=step_into(X,out,a,b,T,h,coeff,dr,dy,src,cp,cm,route);secs=time.monotonic()-start
                err=float(np.max(abs(Y-Z))/max(1.,np.max(abs(Y))));assert err<3e-14
                assert not np.any(Z[..., -1]) and not np.any(Z[4,:,1:]) and not np.any(Z[5,:,:-1])
                rows.append(dict(nr=nr,ny=ny,route=route,t=t,error=err,bitwise=bool(np.array_equal(Y,Z)),seconds=secs))
    return rows
if __name__=='__main__':print(json.dumps(check()),flush=True)
