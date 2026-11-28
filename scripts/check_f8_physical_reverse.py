"""Local exact and native controls for the physical Weyl adjoint restriction."""
import math,json
import numpy as np
import sympy as s
from scipy.optimize import brentq
from ksw668_f8_tt_multipole import F
from ksw668_f8_signed_route_stage import rhs_transpose,reverse_step,step
from f8_physical_reverse import rhs_physical_transpose,reverse_physical,physical_observation,signed_contribution


def check():
    # Exact noncommuting stage matrices with independent history couplings.
    h=s.symbols('h'); I=s.eye(3);A=[]
    for k in range(3):
        a,b,c,d,e,f=s.symbols('a%d b%d c%d d%d e%d f%d'%(k,k,k,k,k,k))
        A.append(I+h*s.Matrix([[a,b,0],[c,d,0],[e,f,0]]))
    E=I/3+s.Rational(2,3)*A[2]*(s.Rational(3,4)*I+A[1]*A[0]/4)
    assert E[:2,2]==s.zeros(2,1) and s.expand(E[2,2])==1
    p=s.Matrix(s.symbols('p:2'));assert (E.T*p.col_join(s.zeros(1,1)))[2]==0
    rng=np.random.default_rng(1547);stage_count=rk_count=ledger_count=0;worst=0.;vjp_worst=0.
    for dr,dy,nr,ny in ((.008,.012,13,5),(.008,.012,378,337),(.006,.009,503,449)):
        src=np.zeros((3,nr));cp=src.copy();cm=src.copy();j=np.arange(1,nr)
        for q,d in enumerate((3,7,11)):
            den=(j+.5)**d-(j-.5)**d;cp[q,1:]=d*(j+.5)**(d-1)/den;cm[q,1:]=d*(j-.5)**(d-1)/den
        for route in ('ledger','paired'):
            for t in (1.,2.,12.):
                T=F(t);dt=.0005999023910881472
                def coeff(T):
                    tt=brentq(lambda u:F(u)-T,.5,25);return -1/math.sqrt(1+tt*tt),1/tt,0.
                y=rng.normal(size=(3,3,ny,nr));y[..., -1]=0
                Y=np.zeros((6,3,ny,nr));Y[:3]=y
                v,b,_=coeff(T);r=rhs_transpose(Y,dr,dy,b,v,route);z=rhs_physical_transpose(y,dr,dy,b,v,route)
                assert np.array_equal(r[:3],z) and not np.any(r[3:]);stage_count+=1
                r=reverse_step(Y,T,dt,coeff,dr,dy,route);z=reverse_physical(y,T,dt,coeff,dr,dy,route)
                assert np.array_equal(r[:3],z) and not np.any(r[3:]);rk_count+=1
                x=rng.normal(size=Y.shape)*.001;x[..., -1]=0
                fx=step(x,T,dt,coeff,dr,dy,src,cp,cm,route)
                a=np.sum(y*fx[:3],axis=(0,2,3));c=np.sum(z*x[:3],axis=(0,2,3))
                budget=np.sum(abs(y*fx[:3]),axis=(0,2,3))+np.sum(abs(z*x[:3]),axis=(0,2,3))
                err=np.max(abs(a-c)/np.maximum(1,budget));assert err<1e-12;vjp_worst=max(vjp_worst,err)
                d=rng.normal(size=Y.shape);d[..., -1]=0
                val=signed_contribution(z,d);full=np.sum(r*d,axis=(2,3));assert np.array_equal(val,full)
                assert np.array_equal(physical_observation(Y),y);ledger_count+=1
                worst=max(worst,float(np.max(abs(r[:3]-z))))
    Y[3,0,0,0]=1
    try:physical_observation(Y)
    except ValueError:pass
    else:raise AssertionError('history observer accepted')
    return dict(stage=stage_count,rk=rk_count,contraction=ledger_count,exact_restriction_max=worst,native_vjp_scaled_error=vjp_worst,history_negative_control=True)

if __name__=='__main__':print(json.dumps(check()))
