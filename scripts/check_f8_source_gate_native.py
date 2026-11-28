import math,json
import numpy as np
from scipy.optimize import brentq
from ksw668_f8_tt_multipole import F
from ksw668_f8_fv_source_flux import exact_cell_averages
from ksw668_f8_signed_route_stage import step
from check_f8_source_inactive_replay import active
T0=F(1);h=(F(12)-T0)/4516

def coeff(T):
    t=brentq(lambda t:F(t)-T,.5,25);v=-1/math.sqrt(1+t*t);q=2*(T-T0)/.065-1
    return v,1/t,-6*math.sqrt(1-v*v)*t*math.exp(1-1/(1-q*q)) if abs(q)<1 else 0.

def check():
    count=0;maxerr=0.;rows=[]
    for dr,dy,nr,ny in ((.008,.012,378,337),(.006,.009,503,449)):
        src=exact_cell_averages(.04,np.arange(nr)*dr,dr);other=-src;cp=np.zeros_like(src);cm=cp.copy()
        for q,d in enumerate((3,7,11)):
            for j in range(1,nr):
                den=(j+.5)**d-(j-.5)**d;cp[q,j]=d*(j+.5)**(d-1)/den;cm[q,j]=d*(j-.5)**(d-1)/den
        for route in ('ledger','paired'):
            with np.load(f'{route}-{nr}-{ny}-prefix.npz',allow_pickle=False) as z:X=z['X'];n=int(z['k'])
            assert n==110
            T=T0+n*h
            assert not active((coeff(T)[2],coeff(T+h)[2],coeff(T+h/2)[2]))
            a=step(X,T,h,coeff,dr,dy,src,cp,cm,route);b=step(X,T,h,coeff,dr,dy,other,cp,cm,route)
            assert np.array_equal(a,b)
            # Counterfactual active clock on the identical state: must not skip.
            T=T0+50*h;assert active((coeff(T)[2],coeff(T+h)[2],coeff(T+h/2)[2]))
            a=step(X,T,h,coeff,dr,dy,src,cp,cm,route);b=step(X,T,h,coeff,dr,dy,other,cp,cm,route)
            diff=float(np.max(abs(a-b)));assert diff>0
            rows.append(dict(route=route,nr=nr,ny=ny,inactive_equal=True,active_max_difference=diff));count+=2
    return dict(checks=count,rows=rows)
if __name__=='__main__':print(json.dumps(check()))
