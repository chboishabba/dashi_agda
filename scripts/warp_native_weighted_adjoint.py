"""Original donor forward stage + separable adjoint, both direct Weyl channels.
No SI calibration or continuum certification."""
import numpy as np
from math import ceil, sqrt, log
from scipy.optimize import brentq
from ksw668_f8_tt_multipole import stage, F
from ksw668_f8_fv_source_flux import exact_cell_averages, total_scaled_moments
from warp_stage_adjoint import transpose, donor_parity

def run(dr=.008,dy=.012,dt=.0015,eps=.04,final_t=12.,pulse=.065,
        r_outer=4.3,y_outer=3.,order=4):
    assert order in (3,4)
    assert 0<dr<eps/3 and 0<dy<=.03 and 0<dt<min(dr*sqrt(3/44),dy*.45)
    t0=F(1); span=F(final_t)-t0; nt=ceil(span/dt); h=span/nt
    rx=sqrt(span**2-(1-1/final_t)**2)-.012
    assert rx-eps-log(final_t)>dr/2
    nr=ceil(r_outer/dr)+1; ny=ceil(y_outer/dy)+1
    rg=np.arange(nr)*dr; src=exact_cell_averages(eps,rg,dr)
    assert np.count_nonzero(np.any(src!=0,axis=0))>3
    cp=np.zeros((3,nr));cm=cp.copy()
    for q in range(3):
        d=3+4*q;j=np.arange(1,nr);den=(j+.5)**d-(j-.5)**d
        cp[q,1:]=d*(j+.5)**(d-1)/den;cm[q,1:]=d*(j-.5)**(d-1)/den
        vol=((rg+dr/2)**d-np.maximum(rg-dr/2,0)**d)/d
        target=total_scaled_moments()['l'+str(2*q)]
        assert abs(vol@src[q]/eps**d-target)<1e-7
    shape=(3,3,ny,nr)
    times=np.arange(2*nt+3)*h/2
    ts=np.array([brentq(lambda t:F(t)-t0-x,.5,final_t+2) for x in times])
    v=-1/np.sqrt(1+ts**2); b=1/ts
    active=(times>0)&(times<pulse); baseline=np.zeros_like(times)
    baseline[active]=-6*np.sqrt(1-v[active]**2)/b[active]*np.exp(1-1/(1-(2*times[active]/pulse-1)**2))
    J=np.zeros(shape); J[2,:,0,:]=-4*h*src/dy; J[..., -1]=0
    def step(x,k,f):
        out=np.empty_like(x)
        stage(*x,*out,dr,dy,b[k],v[k],f,src,cp,cm,order)
        out=x+h*out;out[..., -1]=0
        return out
    def adj(x,k):
        out=x+h*transpose(x,dr,dy,b[k],v[k],order);out[..., -1]=0
        return out
    # Both donor direct Weyl readouts, including the native angular reconstruction.
    ir=int(rx/dr); assert 1<=ir<nr-2
    x=rx/dr-ir
    w=np.array([-x*(x-1)*(x-2)/6,(x+1)*(x-1)*(x-2)/2,-(x+1)*x*(x-2)/2,(x+1)*x*(x-1)/6])
    dw=np.array([-(3*x*x-6*x+2)/6,(3*x*x-4*x-1)/2,(-3*x*x+2*x+2)/2,(3*x*x-1)/6])/dr
    dd=np.array([1-x,3*x-2,1-3*x,x])/dr**2
    S=sqrt(1+final_t**2)/final_t; Se=-1/(final_t*sqrt(1+final_t**2))
    # Four outputs: direct E4/E5 and stage-tangent E4/E5.
    obs={}
    for ch in range(4):
        for n in (nt-1,nt,nt+1):
            o=np.zeros(shape)
            sign=n-nt
            for q in range(3):
                ell=2*q; fac=(rx/eps)**ell
                is5=ch%2; pref=-fac/((2 if is5 else 4)*final_t**2)
                spatial=-(dd+(2*ell+2)*dw/rx) if is5 else dd+2*ell*dw/rx+ell*(ell-1)*w/rx**2
                if n==nt:o[0,q,0,ir-1:ir+3]+=pref*spatial
                linear=Se+2*S*is5
                if ch<2:
                    o[0,q,0,ir-1:ir+3]+=pref*w*(S*S*(1 if sign else -2)/h**2+linear*sign/(2*h))
                else:
                    # stage Udot=.5*((1+v)P+(1-v)M); no direct source term.
                    coeff=pref*w*(S*S*sign/(2*h)+linear*(sign==0))
                    o[1,q,0,ir-1:ir+3]+=coeff*(1+v[2*n])/2
                    o[2,q,0,ir-1:ir+3]+=coeff*(1-v[2*n])/2
            obs[ch,n]=o
    def forward(f):
        x=np.zeros(shape); vals=np.zeros(4)
        for n in range(nt+2):
            if n>=nt-1:
                for ch in range(4):vals[ch]+=np.sum(obs[ch,n]*x)
            if n==nt+1:break
            k=2*n;x1=step(x,k,f[k]);x2=.75*x+.25*step(x1,k+2,f[k+2])
            x=x/3+2/3*step(x2,k+1,f[k+1])
        return vals
    kernels=np.zeros((4,len(times)))
    for ch in range(4):
        lam=obs[ch,nt+1].copy();g=kernels[ch]
        for n in range(nt,-1,-1):
            k=2*n;l2=2/3*adj(lam,k+1);l1=.25*adj(l2,k+2)
            g[k+1]+=2/3*np.sum(J*lam);g[k+2]+=.25*np.sum(J*l2);g[k]+=np.sum(J*l1)
            lam=lam/3+.75*l2+adj(l1,k)
            if n>=nt-1:lam+=obs[ch,n]
    kernels[:,~active]=0
    weights=np.zeros_like(times)
    for n in range(nt+1):weights[2*n:2*n+3]+=h*np.array([1/6,2/3,1/6])
    weights/=(-v*b**3)
    budget=np.dot(weights,baseline**2)
    original=forward(baseline)
    def verify(actual,pred):
        assert np.isfinite(actual).all() and np.isfinite(pred).all()
        np.testing.assert_allclose(actual,pred,rtol=2e-6,atol=1e-13)
    verify(original,kernels@baseline)
    print('grid',nr,ny,nt,'order',order,'original',original,'budget',budget,flush=True)
    for ch,k in enumerate(kernels):
        C=np.dot(k,k/weights);assert C>0
        f=k/weights*np.sqrt(budget/C)
        assert np.isclose(weights@f**2,budget,rtol=1e-12)
        actual=forward(f);verify(actual,kernels@f)
        assert np.isclose(actual[ch],np.sqrt(budget*C),rtol=2e-6,atol=1e-13)
        print('channel',ch,'optimized',actual,'compliance',C,'gain',abs(actual[ch]/original[ch]),flush=True)
if __name__=='__main__':
    import sys,json
    donor_parity()
    run(**(json.loads(sys.argv[1]) if len(sys.argv)>1 else {}))
