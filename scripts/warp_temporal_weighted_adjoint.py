"""Resolved-source driver recovered from PR #1530 native weighted-adjoint formulas."""
from warp_temporal import *
from math import ceil,log
from ksw668_f8_fv_source_flux import exact_cell_averages,total_scaled_moments
import time,json,sys
from numba import set_num_threads
from pathlib import Path

def run(dr=.008,dy=.012,dt=.0015,eps=.04,final_t=12.,pulse=.065,r_outer=4.3,y_outer=3.,order=4,threads=4,mode=None,phase="both",checkpoint="warp_temporal_checkpoint"):
    assert order in (3,4) and phase in ('both','adjoint','forward')
    assert mode is None or (0<=mode<3 and phase!='both')
    set_num_threads(threads);F=lambda t:asinh(t)-sqrt(1+t*t)/t
    span=F(final_t)-F(1);nt=ceil(span/dt);h=span/nt
    rx=sqrt(span**2-(1-1/final_t)**2)-.012
    assert rx-eps-log(final_t)>dr/2
    assert dr<eps/3 and dt<min(dr*sqrt(3/44),dy*.45)
    nr=ceil(r_outer/dr)+1;ny=ceil(y_outer/dy)+1;r=np.arange(nr)*dr
    src=exact_cell_averages(eps,r,dr);assert np.count_nonzero(np.any(src!=0,axis=0))>3
    for q in range(3):
        d=3+4*q;vol=((r+dr/2)**d-np.maximum(r-dr/2,0)**d)/d
        target=total_scaled_moments()["l"+str(2*q)]
        assert abs(vol@src[q]/eps**d-target)<1e-7
    t=np.arange(2*nt+3)*h/2;C=coefficients(t,ny,dy,order);ts,v,b,*_=C;R,RT=radial_bands(nr,dr)
    active=(t>0)&(t<pulse);baseline=np.zeros_like(t)
    baseline[active]=-6*np.sqrt(1-v[active]**2)/b[active]*np.exp(1-1/(1-(2*t[active]/pulse-1)**2))
    obs=np.zeros((4,3,3,3,ny,nr));ir=int(rx/dr);x=rx/dr-ir
    w=np.array([-x*(x-1)*(x-2)/6,(x+1)*(x-1)*(x-2)/2,-(x+1)*x*(x-2)/2,(x+1)*x*(x-1)/6])
    dw=np.array([-(3*x*x-6*x+2)/6,(3*x*x-4*x-1)/2,(-3*x*x+2*x+2)/2,(3*x*x-1)/6])/dr
    dd=np.array([1-x,3*x-2,1-3*x,x])/dr**2;S=sqrt(1+final_t**2)/final_t;Se=-1/(final_t*sqrt(1+final_t**2))
    for ch in range(4):
        for i,n in enumerate((nt-1,nt,nt+1)):
            sign=n-nt
            for q in range(3):
                ell=2*q;fac=(rx/eps)**ell;is5=ch%2;pref=-fac/((2 if is5 else 4)*final_t**2)
                spatial=-(dd+(2*ell+2)*dw/rx) if is5 else dd+2*ell*dw/rx+ell*(ell-1)*w/rx**2
                if n==nt:obs[ch,i,0,q,0,ir-1:ir+3]+=pref*spatial
                linear=Se+2*S*is5
                if ch<2:obs[ch,i,0,q,0,ir-1:ir+3]+=pref*w*(S*S*(1 if sign else -2)/h**2+linear*sign/(2*h))
                else:
                    a=pref*w*(S*S*sign/(2*h)+linear*(sign==0))
                    obs[ch,i,1,q,0,ir-1:ir+3]+=a*(1+v[2*n])/2
                    obs[ch,i,2,q,0,ir-1:ir+3]+=a*(1-v[2*n])/2
    print('grid',nr,ny,nt,'photon margin',rx-eps-log(final_t)-dr/2,flush=True)
    checkpoint=Path(checkpoint);checkpoint.mkdir(exist_ok=True,parents=True)
    config=dict(dr=dr,dy=dy,dt=dt,eps=eps,final_t=final_t,pulse=pulse,
                r_outer=r_outer,y_outer=y_outer,order=order,nr=nr,ny=ny,nt=nt)
    manifest=checkpoint/'manifest.json'
    if manifest.exists():
        assert json.loads(manifest.read_text())==config, 'checkpoint configuration mismatch'
    else:
        assert not list(checkpoint.glob('*.npy')), 'unidentified checkpoint arrays'
        manifest.write_text(json.dumps(config,sort_keys=True))
    modes=range(3) if mode is None else [mode]
    def one(q, controls, adj):
        return propagate(controls,np.ascontiguousarray(obs[:,:,:,q:q+1]),h,dy,R[q:q+1],RT[q:q+1],C,src[q:q+1],adj)
    start=time.monotonic()
    if phase in ('both','adjoint'):
        for q in modes:
            gq=one(q,np.empty((0,len(t))),True);gq[:,~active]=0
            np.save(checkpoint/f'kernel{q}.npy',gq)
            for old in checkpoint.glob('forward*.npy'):old.unlink()
            print('adjoint mode',q,'seconds',time.monotonic()-start,flush=True)
        if phase=='adjoint':return
    g=sum(np.load(checkpoint/f'kernel{q}.npy') for q in range(3))
    print('adjoint seconds',time.monotonic()-start,flush=True)
    weights=np.zeros_like(t)
    for n in range(nt+1):weights[2*n:2*n+3]+=h*np.array([1/6,2/3,1/6])
    weights/=(-v*b**3);budget=weights@baseline**2;compliance=np.sum(g*g/weights,axis=1)
    opt=g/weights*np.sqrt(budget/compliance)[:,None];f=np.vstack((baseline,opt))
    np.testing.assert_allclose(np.sum(f*f*weights,axis=1),budget,rtol=1e-12)
    print('budget',budget,'compliance',compliance,'prediction',f@g.T,flush=True)
    start=time.monotonic()
    for q in modes:
        aq=one(q,f,False);np.save(checkpoint/f'forward{q}.npy',aq)
        print('forward mode',q,'seconds',time.monotonic()-start,flush=True)
    if not all((checkpoint/f'forward{q}.npy').exists() for q in range(3)):return
    actual=sum(np.load(checkpoint/f'forward{q}.npy') for q in range(3));pred=f@g.T
    np.testing.assert_allclose(actual,pred,rtol=2e-6,atol=1e-13)
    print('forward seconds',time.monotonic()-start,'actual',actual,'max abs',np.max(abs(actual-pred)),flush=True)
    print('amplitude ratios',abs(np.diag(actual[1:])/actual[0]),flush=True)
if __name__=='__main__':run(**(json.loads(sys.argv[1]) if len(sys.argv)>1 else {}))
