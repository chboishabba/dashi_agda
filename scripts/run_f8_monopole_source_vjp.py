"""All radial source-cell cotangents for one original far raw E4 consumer.
Ledger monopole, physical-only transpose, prescribed compact source clocks.
The source kernel acts on cell values, not shell masses. No forward histories deleted.
"""
import argparse,hashlib,json,math,os,time
from pathlib import Path
import numpy as np
from numba import njit,prange
from scipy.optimize import brentq
from ksw668_f8_tt_multipole import F
from warp_stage_adjoint import transpose
from warp_native_geometric_receiver import receiver_bank
from run_f8_fused_forward import digest
from run_f8_monopole_shadow import maps
from ksw668_f8_fv_source_flux import exact_cell_averages


def coefficients(nr,dr):
    j=np.arange(1,nr-1,dtype=float);p=np.zeros(nr);m=p.copy();p[0]=6
    den=(j+.5)**3-(j-.5)**3;p[1:-1]=3*(j+.5)**2/den;m[1:-1]=3*(j-.5)**2/den
    return p/dr**2,m/dr**2


def normal_coeff(ny,dy,b):
    z=b+dy*np.arange(ny);d=1.5/z;d[0]-=1/dy;d[-1]+=1/dy
    lo=np.zeros(ny);hi=lo.copy();lo[1:]=.5/dy*(z[:-1]/z[1:])**1.5;lo[1]*=2
    hi[:-1]=-.5/dy*(z[1:]/z[:-1])**1.5;hi[-2]*=2
    return z,d,lo,hi


@njit(cache=True,parallel=True)
def bt(X,out,h,scale,dy,v,p,m,z,d,lo,hi):
    _,ny,nr=X.shape;a=1+v;c=1-v
    for i in prange(ny):
        for j in range(nr-1):
            u,pp,mm=X[0,i,j],X[1,i,j],X[2,i,j];sm=pp+mm
            ru=-(p[j]+m[j])*sm
            if j:ru+=p[j-1]*(X[1,i,j-1]+X[2,i,j-1])
            if j<nr-2:ru+=m[j+1]*(X[1,i,j+1]+X[2,i,j+1])
            dp=d[i]*pp;dm=d[i]*mm
            if i:dp+=lo[i]*X[1,i-1,j];dm+=lo[i]*X[2,i-1,j]
            if i<ny-1:dp+=hi[i]*X[1,i+1,j];dm+=hi[i]*X[2,i+1,j]
            rp=a*u/2+a*dp-1.5*sm/z[i];rm=c*u/2-c*dm+1.5*sm/z[i]
            if i==ny-1:rp-=2*a*pp/dy
            if i==0:rp+=2*a*mm/dy;rm-=2*c*mm/dy
            out[0,i,j]=scale*(u+h*ru);out[1,i,j]=scale*(pp+h*rp);out[2,i,j]=scale*(mm+h*rm)
        for q in range(3):out[q,i,-1]=0


@njit(cache=True,parallel=True)
def combine(L,A,B):
    for i in prange(L.shape[1]):
        for c in range(3):
            for j in range(L.shape[2]):L[c,i,j]=L[c,i,j]/3+3*A[c,i,j]/4+B[c,i,j]


def check():
    rng=np.random.default_rng(1547);worst=0.;checks=0
    for nr,ny in ((17,5),(503,449)):
        p,m=coefficients(nr,.006);x=rng.normal(size=(3,ny,nr));x[..., -1]=0;out=np.empty_like(x)
        for t in (1.,2.,12.):
            b=1/t;v=-1/math.sqrt(1+t*t);h=.0005999023910881472
            bt(x,out,h,1.,.009,v,p,m,*normal_coeff(ny,.009,b))
            ref=x+h*transpose(x[:,None],.006,.009,b,v,4)[:,0]
            e=float(np.max(abs(ref-out))/max(1.,np.max(abs(ref))));assert e<1e-13;worst=max(worst,e);checks+=1
    return dict(checks=checks,max_scaled=worst)


def run(work,budget):
    dr,dy,nr,ny=.006,.009,503,449;T0=F(1);span=F(12)-T0;nt=math.ceil(span/.0006);h=span/nt;end=nt+1
    def coeff(T):
        t=brentq(lambda t:F(t)-T,.5,25);v=-1/math.sqrt(1+t*t);q=2*(T-T0)/.065-1
        return v,1/t,-6*math.sqrt(1-v*v)*t*math.exp(1-1/(1-q*q)) if abs(q)<1 else 0.
    vel=np.array([coeff(T0+i*h/2)[0] for i in range(2*end+1)])
    rx=math.sqrt(span**2-(1-1/12)**2)+.1;bank=receiver_bank(12,rx,.04,dr,dy,h,vel,nt,nr,3)[0,:,:,0]
    p,m=coefficients(nr,dr);L=np.zeros((3,ny,nr));L[:,:3]=bank[-1];grad=np.zeros(nr);absolute=np.zeros(nr);k=end
    ident=json.dumps(dict(dt=h,grid=[nr,ny],rx=rx,bank=digest(bank),code={n:hashlib.sha256(Path(__file__).with_name(n).read_bytes()).hexdigest() for n in ('run_f8_monopole_source_vjp.py','warp_stage_adjoint.py','warp_native_geometric_receiver.py','ksw668_f8_tt_multipole.py')}),sort_keys=True)
    path=work/'ledger-far-e4-source-vjp.npz'
    if path.exists():
        with np.load(path,allow_pickle=False) as z:
            assert z['identity'].item()==ident;k=int(z['k']);L=z['L'];grad=z['grad'];absolute=z['absolute'];assert all(digest(v)==z[n+'_sha'].item() for n,v in [('L',L),('grad',grad),('absolute',absolute)])
    A,B,C=[np.empty_like(L) for _ in range(3)];start=time.monotonic();initial=k
    while k>0:
        n=k-1;T=T0+n*h;v2,b2,a2=coeff(T+h/2);v1,b1,a1=coeff(T+h);v0,b0,a0=coeff(T)
        bt(L,A,h,2/3,dy,v2,p,m,*normal_coeff(ny,dy,b2))
        bt(A,B,h,1/4,dy,v1,p,m,*normal_coeff(ny,dy,b1))
        bt(B,C,h,1.,dy,v0,p,m,*normal_coeff(ny,dy,b0))
        # Each stage source column has only the wall M component -4*amp/dy.
        if a0 or a1 or a2:
            q2=(-4*h/dy)*(2/3)*a2*L[2,0];q1=(-4*h/dy)*.25*a1*A[2,0];q0=(-4*h/dy)*a0*B[2,0]
            grad+=q2+q1+q0;absolute+=abs(q2)+abs(q1)+abs(q0)
        combine(L,A,C);k=n
        if nt-1<=k<=end:L[:,:3]+=bank[k-nt+1]
        if k%128==0 or k==0 or time.monotonic()-start>=budget:
            assert np.isfinite(L).all() and not np.any(L[...,-1]);arrays=dict(L=L,grad=grad,absolute=absolute);sha={n+'_sha':digest(v) for n,v in arrays.items()};tmp=path.with_suffix('.tmp')
            with tmp.open('wb') as f:np.savez(f,identity=ident,k=k,**arrays,**sha);f.flush();os.fsync(f.fileno())
            os.replace(tmp,path)
            with np.load(path,allow_pickle=False) as z:assert int(z['k'])==k and z['identity'].item()==ident and all(digest(z[n])==sha[n+'_sha'] for n in arrays)
            if time.monotonic()-start>=budget:break
    result=dict(initial=initial,cursor=k,seconds=time.monotonic()-start,sha256=digest(L),complete=k==0)
    if k==0:
        I,_,wc,wf=maps();gc=exact_cell_averages(.04,np.arange(378)*.008,.008)[0,:-1];gf=exact_cell_averages(.04,np.arange(503)*.006,.006)[0,:-1];delta=gf-I@gc
        contrib=grad[:-1]*delta;result.update(source_total=float(contrib.sum()),fine_pred=float(grad[:-1]@gf),shadow_pred=float(grad[:-1]@(I@gc)),source_cells=[dict(index=int(j),r=j*dr,delta=float(delta[j]),kernel=float(grad[j]),signed=float(contrib[j]),stage_absolute=float(absolute[j]*abs(delta[j]))) for j in np.flatnonzero(delta)],kernel=grad.tolist())
    return result

if __name__=='__main__':
    a=argparse.ArgumentParser();a.add_argument('work',type=Path);a.add_argument('--budget',type=float,default=12);a.add_argument('--check',action='store_true');a=a.parse_args();assert 0<a.budget<=75;print(json.dumps(check() if a.check else run(a.work,a.budget)),flush=True)
