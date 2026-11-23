"""Native mode-3 stage residual ledger on a reduced-box time prefix.
Uses #1530 warp_stage_adjoint, original compact source and stage operator.
Not a physical receiver run or continuum convergence certificate.
"""
import math
import numpy as np
from scipy.optimize import brentq
from ksw668_f8_fv_source_flux import exact_cell_averages
from warp_stage_adjoint import transpose
from ksw668_f8_tt_multipole import stage


def run():
    h=.0011998047821762945; dy=.012; nt=40; ny=9
    drc,drf=.008,.006; nc,nf=16,21; eps=.04
    F=lambda t:math.asinh(t)-math.sqrt(1+t*t)/t
    t0=F(1)
    def coeff(n):
        ds=n*h;t=brentq(lambda t:F(t)-t0-ds,1,2)
        v=-1/math.sqrt(1+t*t);b=1/t
        amp=-6*math.sqrt(1-v*v)/b*math.exp(1-1/(1-(2*ds/.065-1)**2)) if 0<ds<.065 else 0.
        return t,b,v,amp
    times=[coeff(j/2) for j in range(2*(nt+1)+1)]
    def setup(dr,nr):
        src=exact_cell_averages(eps,np.arange(nr)*dr,dr);cp=np.zeros((3,nr));cm=cp.copy();j=np.arange(1,nr)
        for q in range(3):
            d=3+4*q;den=(j+.5)**d-(j-.5)**d
            cp[q,1:]=d*(j+.5)**(d-1)/den;cm[q,1:]=d*(j-.5)**(d-1)/den
        return dr,nr,src,cp,cm
    C,Fg=setup(drc,nc),setup(drf,nf)
    def rhs(x,k,G,forced=True):
        dr,nr,src,cp,cm=G;t,b,v,amp=times[k];o=np.empty_like(x)
        stage(*x,*o,dr,dy,b,v,amp if forced else 0.,src,cp,cm,3);return o
    def B(x,k,G,forced=True):return x+h*rhs(x,k,G,forced)
    def step(x,n,G,forced=True):
        k=2*n;x1=B(x,k,G,forced);x2=.75*x+.25*B(x1,k+2,G,forced)
        return (x+2*B(x2,k+1,G,forced))/3
    def BT(y,k,G):
        dr=G[0];t,b,v,a=times[k];return y+h*transpose(y,dr,dy,b,v,3)
    def reverse(y,n,G):
        k=2*n;l2=2/3*BT(y,k+1,G);l1=BT(l2,k+2,G)/4
        return y/3+.75*l2+BT(l1,k,G)
    rng=np.random.default_rng(1527);mx=0.
    for G in (C,Fg):
        for k in (0,1,27,80):
            x=rng.normal(size=(3,3,ny,G[1]));y=rng.normal(size=x.shape);x[...,-1]=0;y[...,-1]=0
            t,b,v,a=times[k];p=np.vdot(rhs(x,k,G,False),y);q=np.vdot(x,transpose(y,G[0],dy,b,v,3));err=abs(p-q)/max(abs(p),abs(q),1.);mx=max(mx,err);assert err<1e-11
        for n in (0,13,39):
            p=np.vdot(step(x,n,G,False),y);q=np.vdot(x,reverse(y,n,G));assert np.isclose(p,q,rtol=1e-11,atol=1e-11)
    maps=[]
    for q in range(3):
        d=3+4*q;c=np.arange(nc-1)*drc;f=np.arange(nf-1)*drf
        a=np.maximum(np.maximum(0,c-drc/2)[None,:],np.maximum(0,f-drf/2)[:,None]);b=np.minimum((c+drc/2)[None,:],(f+drf/2)[:,None]);O=np.where(b>a,(b**d-a**d)/d,0)
        wf=((f+drf/2)**d-np.maximum(0,f-drf/2)**d)/d;maps.append(O/wf[:,None])
    def transfer(x):
        y=np.zeros((3,3,ny,nf))
        for q,I in enumerate(maps):y[:,q,:,:-1]=x[:,q,:,:-1]@I.T
        return y
    def history(G):
        x=np.zeros((3,3,ny,G[1]));out=[x]
        for n in range(nt+1):x=step(x,n,G);out.append(x)
        return out
    xc,xf=history(C),history(Fg);mapped=list(map(transfer,xc));res=[mapped[n+1]-step(mapped[n],n,Fg) for n in range(nt+1)]
    # Actual corrected receiver formula, diagnostic interior point and time.
    rx=.08;t=times[2*nt][0];S=math.sqrt(1+t*t)/t;Se=-1/(t*math.sqrt(1+t*t));ir=int(rx/drf);a=rx/drf-ir
    w=np.array([-a*(a-1)*(a-2)/6,(a+1)*(a-1)*(a-2)/2,-(a+1)*a*(a-2)/2,(a+1)*a*(a-1)/6]);dw=np.array([-(3*a*a-6*a+2)/6,(3*a*a-4*a-1)/2,(-3*a*a+2*a+2)/2,(3*a*a-1)/6])/drf;dd=np.array([1-a,3*a-2,1-3*a,a])/drf**2
    sl=slice(ir-1,ir+3);rows=[]
    for q in range(3):
        ell=2*q;fac=(rx/eps)**ell;lap=dd+(2*ell+2)*dw/rx
        for ch in range(4):
            is5=ch%2;pref=-fac/((2 if is5 else 4)*t*t);lin=Se+2*S*is5
            W={n:np.zeros_like(xf[0]) for n in (nt-1,nt,nt+1)}
            for n,o in W.items():
                sign=n-nt
                if n==nt:o[0,q,0,sl]+=pref*lap*(-1 if is5 else 1)
                if ch<2:o[0,q,0,sl]+=pref*w*(S*S*(1 if sign else -2)/h**2+lin*sign/(2*h))
                else:
                    v=times[2*n][2];co=pref*w*(S*S*sign/(2*h)+lin*(sign==0));o[1,q,0,sl]+=co*(1+v)/2;o[2,q,0,sl]+=co*(1-v)/2
            expected=sum(np.vdot(o,mapped[n]-xf[n]) for n,o in W.items());lam=W[nt+1].copy();terms=[]
            for n in range(nt,-1,-1):
                terms.append(np.vdot(lam,res[n]));lam=reverse(lam,n,Fg)
                if n in W:lam+=W[n]
            signed=sum(terms);absolute=sum(map(abs,terms));err=abs(signed-expected)/max(absolute,1e-300);assert err<1e-8,(q,ch,err)
            rows.append((ell,ch,float(expected),float(signed),float(absolute),float(err)))
    print('stage transpose max relative',mx,'; 6 RK transpose checks passed')
    for row in rows:print(row)
    print('12 ledgers max normalized closure',max(r[-1] for r in rows),'steps',nt+1,'physical t',t)
if __name__=='__main__':run()
