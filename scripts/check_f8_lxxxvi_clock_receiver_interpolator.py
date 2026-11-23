"""F8 LXXXVI local physical-clock and production cubic interpolation seam.

Uses original native F and diagnostic receiver geometry; no production PDE run.
Brent inversion is compared with high precision numerically, not interval-certified.
"""
import json,math
from scipy.optimize import brentq
import numpy as np
import mpmath as mp
from ksw668_f8_tt_multipole import F
mp.mp.dps=90

def clock():
    h=.001
    ts=[brentq(lambda t:F(t)-F(1)-.02-k*h/2,.5,3,xtol=5e-15) for k in range(9)]
    def f(t):return mp.asinh(t)-mp.sqrt(1+t*t)/t
    exact=[mp.findroot(lambda t:f(t)-(f(mp.mpf(1))+mp.mpf('.02')+mp.mpf(k)/2000),(mp.mpf('1.01'),mp.mpf('1.5'))) for k in range(9)]
    return dict(t=max(float(abs(mp.mpf(x)-y)) for x,y in zip(ts,exact)),
        b=max(float(abs(mp.mpf(1/x)-1/y)) for x,y in zip(ts,exact)),
        v=max(float(abs(mp.mpf(-1/math.sqrt(1+x*x))+1/mp.sqrt(1+y*y))) for x,y in zip(ts,exact)))

def interpolate():
    results=[]
    for dr,rx,nr in ((.008,.053,13),(.008,.073,13),(.008,.081,15),
                     (.004,.053,25),(.004,.073,25),(.004,.081,25)):
        x=rx/dr;j=int(math.floor(x));q=x-j
        ids=np.arange(j-1,j+3)
        V=(ids-x)[None,:]**np.arange(4)[:,None]
        rhs=np.zeros((4,3));rhs[0,0]=1;rhs[1,1]=1/dr;rhs[2,2]=2/dr**2
        w,dw,dd=np.linalg.solve(V,rhs).T
        prodw=np.array([-q*(q-1)*(q-2)/6,(q+1)*(q-1)*(q-2)/2,
                        -(q+1)*q*(q-2)/2,(q+1)*q*(q-1)/6])
        proddw=np.array([-(3*q*q-6*q+2)/6,(3*q*q-4*q-1)/2,
                         (-3*q*q+2*q+2)/2,(3*q*q-1)/6])/dr
        proddd=np.array([1-q,3*q-2,1-3*q,q])/dr**2
        err=[float(np.max(abs(a-b))) for a,b in zip((w,dw,dd),(prodw,proddw,proddd))]
        assert max(err)<1e-9
        results.append(dict(dr=dr,rx=rx,errors=err))
    return results

if __name__=="__main__":
    a=clock(); b=interpolate()
    print(json.dumps(dict(status="PASS",clock=a,
        max_production_cubic_vs_diagnostic=[max(row["errors"][k] for row in b) for k in range(3)],
        cases=b,scope="Measured finite-fixture comparison. No certified clock, physical trajectory, full production 96-output receiver or floating propagation bound."),indent=2))
