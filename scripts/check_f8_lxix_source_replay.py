import math,sys,json,time
from pathlib import Path
import numpy as np
from ksw668_f8_tt_multipole import stage
from ksw668_f8_fv_source_flux import exact_cell_averages
from ksw668_f8_weak_source import weak_source

def run(label,budget=12):
    dr=.008 if label[0]=='A' else .006
    weak=label[1]=='1'; dy=.012; eps=.04; final_t=12.; pulse=.065
    F=lambda t:math.asinh(t)-math.sqrt(1+t*t)/t
    T0=F(1);span=F(final_t)-T0;nt=math.ceil(span/.0012);dt=span/nt
    bulk=math.sqrt(span*span-(1-1/final_t)**2);rx=bulk-.012
    nr=math.ceil(3.01/dr)+1;ny=math.ceil(2.01/dy)+1
    rg=np.arange(nr)*dr;src=(weak_source if weak else exact_cell_averages)(eps,rg,dr)
    if weak: assert rx-math.log(final_t)-(rg[np.flatnonzero(np.any(src!=0,axis=0))[-1]]+dr)>dr/2
    cp=np.zeros((3,nr));cm=cp.copy()
    for q in range(3):
        d=3+4*q
        for j in range(1,nr):
            den=(j+.5)**d-(j-.5)**d;cp[q,j]=d*(j+.5)**(d-1)/den;cm[q,j]=d*(j-.5)**(d-1)/den
    def coeff(T):
        t=max(1.,math.exp(T+1)/2)
        for _ in range(7):
            t-=(F(t)-T)/(math.sqrt(1+t*t)/t**2)
            if t<.5:t=.5
        v=-1/math.sqrt(1+t*t);b=1/t;ds=T-T0;q=2*ds/pulse-1
        amp=-6*math.sqrt(1-v*v)/b*math.exp(1-1/(1-q*q)) if 0<ds<pulse else 0.
        return v,b,amp
    shape=(3,3,ny,nr); X=np.zeros(shape);O=np.empty_like(X); hist=np.zeros((3,2,3,nr));cursor=0
    path=Path(label+'.npz')
    if path.exists():
        with np.load(path,allow_pickle=False) as z:
            assert np.array_equal(z['src'],src);cursor=int(z['cursor']);X=z['X'];hist=z['hist']
    def rhs(x,T):
        v,b,a=coeff(T);stage(*x,*O,dr,dy,b,v,a,src,cp,cm,3)
    begin=time.monotonic()
    for n in range(cursor,nt+1):
        T=T0+n*dt;rhs(X,T)
        if n in (nt-1,nt):hist[n-nt+1,0]=X[0,:,0,:];hist[n-nt+1,1]=O[0,:,0,:]
        X1=X+dt*O;rhs(X1,T+dt);X2=.75*X+.25*(X1+dt*O);rhs(X2,T+dt/2);X=(X+2*(X2+dt*O))/3
        if (n+1)%16==0 and time.monotonic()-begin>budget or n==nt:
            tmp=path.with_suffix('.tmp.npz');np.savez(tmp,cursor=n+1,X=X,hist=hist,src=src);tmp.replace(path)
            if n<nt: print(label,n+1,nt+1,flush=True);return False
    rhs(X,T0+(nt+1)*dt);hist[2,0]=X[0,:,0,:];hist[2,1]=O[0,:,0,:]
    assert np.isfinite(X).all()
    def read(r):
        x=r/dr;ir=math.floor(x);q=x-ir
        w=np.array([-q*(q-1)*(q-2)/6,(q+1)*(q-1)*(q-2)/2,-(q+1)*q*(q-2)/2,(q+1)*q*(q-1)/6]);dw=np.array([-(3*q*q-6*q+2)/6,(3*q*q-4*q-1)/2,(-3*q*q+2*q+2)/2,(3*q*q-1)/6])/dr;dd=np.array([1-q,3*q-2,1-3*q,q])/dr**2
        sl=slice(ir-1,ir+3);S=math.sqrt(1+final_t**2)/final_t;Se=-1/(final_t*math.sqrt(1+final_t**2)); rows=[]
        for j in range(3):
            ell=2*j;fac=(r/eps)**ell;h=fac*(hist[:,0,j,sl]@w);ht=fac*(hist[:,1,j,sl]@w);L=fac*np.dot(dd+(2*ell+2)*dw/r,hist[1,0,j,sl]);H=(h[2]-h[0])/(2*dt);A=S*S*(h[2]-2*h[1]+h[0])/dt**2+Se*H;At=S*S*(ht[2]-ht[0])/(2*dt)+Se*ht[1]
            rows.append([-(A+L)/(4*final_t**2),-(A+2*S*H-L)/(2*final_t**2),-(At+L)/(4*final_t**2),-(At+2*S*ht[1]-L)/(2*final_t**2)])
        return rows
    result=dict(label=label,nt=nt+1,dt=dt,shape=shape,near=read(rx),far=read(bulk+.1));Path(label+'.json').write_text(json.dumps(result,indent=2));print(json.dumps(result),flush=True);return True
if __name__=='__main__':run(sys.argv[1])
