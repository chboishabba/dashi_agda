"""Small-box pulse parity; not physical receiver or stability acceptance."""
import numpy as np
import math
from ksw668_f8_tt_multipole import stage,affine_mode3_stage,enforce,F
from ksw668_f8_fv_source_flux import exact_cell_averages

def check():
    nr=17; ny=17; dr=.008; dy=.02; dt=.0005
    src=exact_cell_averages(.04,np.arange(nr)*dr,dr)
    cp=np.zeros_like(src);cm=np.zeros_like(src)
    for q in range(3):
        d=3+4*q
        for j in range(1,nr):
            den=(j+.5)**d-(j-.5)**d
            cp[q,j]=d*(j+.5)**(d-1)/den;cm[q,j]=d*(j-.5)**(d-1)/den
    T0=F(1)
    def coeff(T):
        t=max(1.,math.exp(T+1)/2)
        for _ in range(7):
            t-=(F(t)-T)/(math.sqrt(1+t*t)/t**2)
            if t<.5:t=.5
        v=-1/math.sqrt(1+t*t);b=1/t;ds=T-T0;q=2*ds/.065-1
        amp=-6*math.sqrt(1-v*v)/b*math.exp(1-1/(1-q*q)) if 0<ds<.065 else 0.
        return v,b,amp
    def rhs(X,T,aff):
        U,P,M=X;v,b,amp=coeff(T);enforce(U,P,M,v,amp,src,3)
        out=np.empty_like(X)
        args=(U,P,M,*out,dr,dy,b,v,amp,src,cp,cm,3)
        if aff:affine_mode3_stage(stage,*args)
        else:stage(*args)
        return out
    def step(X,T,aff):
        X1=X+dt*rhs(X,T,aff)
        X2=.75*X+.25*(X1+dt*rhs(X1,T+dt,aff))
        return (X+2*(X2+dt*rhs(X2,T+dt/2,aff)))/3
    A=np.zeros((3,3,ny,nr));B=A.copy();mx=0.
    for n in range(160):
        A=step(A,T0+n*dt,False);B=step(B,T0+n*dt,True)
        np.testing.assert_allclose(A,B,atol=1e-9,rtol=1e-10)
        mx=max(mx,float(np.max(abs(A-B))))
    print('160/160 step states PASS; max absolute',mx,'max state',abs(A).max())
if __name__=='__main__':check()
