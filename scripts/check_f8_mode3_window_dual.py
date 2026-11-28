"""Actual original mode3 common-clock reverse source contraction.
Optimized gather form of existing warp_stage_adjoint.transpose (mode3),
Shu-Osher reverse composition from ksw668_f8_signed_route_stage.reverse_step.
Finite algebra and numerical duality, NOT interval propagation or continuum B.
"""
import argparse,hashlib,json,math,time
from pathlib import Path
import numpy as np
from numba import njit
from scipy.integrate import quad
import ksw668_f8_tt_multipole as original
from ksw668_f8_fv_source_flux import exact_cell_averages
from ksw668_f8_weak_source import weak_source
from run_f8_common_clock_capture import T0,Tend,nt,dt,bulk,weight
from check_f8_parity_capture_tail import geometry_rows,radial_rows
from run_f8_p0_native_receiver_state_capture import atomic_npz


def coeff(T):
    t=max(1.,math.exp(T+1)/2)
    for _ in range(7):
        t-=(original.F(t)-T)/(math.sqrt(1+t*t)/t**2)
        if t<.5:t=.5
    v=-1/math.sqrt(1+t*t);b=1/t;ds=T-T0;q=2*ds/.065-1
    amp=-6*math.sqrt(1-v*v)/b*math.exp(1-1/(1-q*q)) if 0<ds<.065 else 0.
    return b,v,amp


def coefficients(nr):
    cp=np.zeros((3,nr));cm=cp.copy()
    for q in range(3):
        d=3+4*q;j=np.arange(1,nr);den=(j+.5)**d-(j-.5)**d
        cp[q,1:]=d*(j+.5)**(d-1)/den;cm[q,1:]=d*(j-.5)**(d-1)/den
    return cp,cm


@njit(cache=True)
def euler_transpose(y,out,dr,h,b,v,cp,cm,step):
    a,c=1+v,1-v;_,nm,ny,nr=y.shape;d2=dr*dr
    for q in range(nm):
        d=3+4*q
        for j in range(ny):
            z=b+j*h
            for k in range(nr-1):
                u,p,m=y[0,q,j,k],y[1,q,j,k],y[2,q,j,k];s=p+m
                radial=-(2*d if k==0 else cp[q,k]+cm[q,k])*s
                if k>0:radial+=(2*d if k==1 else cp[q,k-1])*(y[1,q,j,k-1]+y[2,q,j,k-1])
                if k<nr-2:radial+=cm[q,k+1]*(y[1,q,j,k+1]+y[2,q,j,k+1])
                dp=0.;dm=0.
                if j>0:
                    f=1. if j==1 else .5
                    dp+=f*y[1,q,j-1,k];dm+=f*y[2,q,j-1,k]
                if j<ny-1:
                    f=1. if j==ny-2 else .5
                    dp-=f*y[1,q,j+1,k];dm-=f*y[2,q,j+1,k]
                if j==0:dp-=p;dm-=m
                if j==ny-1:dp+=p;dm+=m
                pd=a*u/2+a*dp/h-1.5*s/z;md=c*u/2-c*dm/h+1.5*s/z
                if j==0:pd+=2*a*m/h;md-=2*c*m/h
                if j==ny-1:pd-=2*a*p/h
                out[0,q,j,k]=u+step*radial/d2;out[1,q,j,k]=p+step*pd;out[2,q,j,k]=m+step*md
            out[:,:,j,nr-1]=0.


def test():
    rng=np.random.default_rng(369);shape=(3,3,7,11);cp,cm=coefficients(11);src=np.zeros((3,11));checks=[]
    for t in (1.,2.,12.):
        b=1/t;v=-1/math.sqrt(1+t*t);x=rng.normal(size=shape);x[..., -1]=0;y=rng.normal(size=shape);y[..., -1]=0;z=np.empty_like(x);adj=np.empty_like(x)
        original.stage(*x,*z,.008,.012,b,v,0.,src,cp,cm,3)
        euler_transpose(y,adj,.008,.012,b,v,cp,cm,dt)
        a=float(np.sum((x+dt*z)*y));c=float(np.sum(x*adj));err=abs(a-c)/(1+abs(a)+abs(c));assert err<2e-14;checks.append(err)
    return checks


def observer(shape,b,v,h,dr,cp,cm,kind,rx):
    t=1/b;a,c=1+v,1-v;ids,w,L,X=radial_rows(rx,dr,.04,shape[-1]);rows=geometry_rows(t)
    o=np.zeros(shape);seed=np.zeros(shape)
    if kind=='gap':
        A,B,D,E,Y,lap,ax=rows[2];d=np.array([-1.,2.,-1.,0.,0.])/h;y=np.array([3.,-8.,6.,0.,-1.])/(4*h*h)
        A=B=lap=ax=0.
    elif kind=='parity_sms':
        A,B,D,E,Y,lap,ax=rows[2]-rows[3];d=np.array([-1.,0.,1.,0.,0.])/(2*h);y=np.array([1.,0.,-2.,0.,1.])/(4*h*h)
    else:raise ValueError(kind)
    for k in range(5):
        o[0,:,k,:][:,ids]+=w*(D*d[k]+Y*y[k]);o[1,:,k,:][:,ids]+=a*w*E*d[k]/2;o[2,:,k,:][:,ids]+=c*w*E*d[k]/2
    o[0,:,0,:][:,ids]+=lap*L+ax*X;o[1,:,0,:][:,ids]+=w*(A*a/2+B*t**3/(1+t*t)**2/2);o[2,:,0,:][:,ids]+=w*(A*c/2-B*t**3/(1+t*t)**2/2)
    if B:
        seed[1,:,0,:][:,ids]=B*a*w/2;seed[2,:,0,:][:,ids]=B*c*w/2
        z=np.empty_like(seed);euler_transpose(seed,z,dr,h,b,v,cp,cm,1.);o+=z-seed
    return o


def run(work,kind,budget):
    dr=.008;h=.012;nr=math.ceil(3.01/dr)+1;ny=math.ceil(2.01/h)+1;shape=(3,3,ny,nr);cp,cm=coefficients(nr);rg=np.arange(nr)*dr
    src=np.stack([exact_cell_averages(.04,rg,dr),weak_source(.04,rg,dr)]);src[..., -1]=0
    identity=json.dumps(dict(kind=kind,dt=dt,dr=dr,dy=h,src_sha256=hashlib.sha256(src.tobytes()).hexdigest(),code_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),solver_sha256=hashlib.sha256(Path(original.__file__).read_bytes()).hexdigest()),sort_keys=True)
    work.mkdir(parents=True,exist_ok=True);p=work/(kind+'.dual.npz');lam=np.zeros(shape);terms=np.zeros((nt,3,2,3));n=nt-1
    if p.exists():
        with np.load(p,allow_pickle=False) as z:
            assert z['identity'].item()==identity;lam=z['lam'].copy();terms=z['terms'].copy();n=int(z['n'].item())
    l2=np.empty_like(lam);l1=np.empty_like(lam);l0=np.empty_like(lam);norm=quad(lambda x:math.exp(1-1/(1-x*x)),-1,1,epsabs=1e-13)[0]*.1
    start=time.monotonic()
    def source_term(y,amp,fac):return (-4*dt/h)*amp*fac*np.einsum('qr,sqr->sq',y[2,:,0,:],src)
    while n>=0:
        T=T0+n*dt;b0,v0,g0=coeff(T);b1,v1,g1=coeff(T+dt);bh,vh,gh=coeff(T+dt/2)
        euler_transpose(lam,l2,dr,h,bh,vh,cp,cm,dt);l2*=2/3
        euler_transpose(l2,l1,dr,h,b1,v1,cp,cm,dt);l1*=.25
        euler_transpose(l1,l0,dr,h,b0,v0,cp,cm,dt)
        if g0 or g1 or gh:
            terms[n,0]=source_term(l1,g0,1.);terms[n,1]=source_term(l2,g1,.25);terms[n,2]=source_term(lam,gh,2/3)
        lam=lam/3+.75*l2+l0
        w=weight(T)
        if w:lam+=dt*w/norm*observer(shape,b0,v0,h,dr,cp,cm,kind,bulk-.012)
        n-=1
        if (nt-n)%32==0 and time.monotonic()-start>=budget:break
    assert np.isfinite(lam).all() and np.isfinite(terms).all();atomic_npz(p,identity=identity,n=n,lam=lam,terms=terms);print(kind,'remaining',n,flush=True)
    if n>=0:return 75
    signed=terms.sum(axis=(0,1));absolute=abs(terms).sum(axis=(0,1));actual=[]
    for label in ('A0','A1'):
        d=json.loads((work/(label+'.axis.json')).read_text());a=np.array(d['window_signed']);actual.append(a[0,0,2]-a[0,1,2] if kind=='gap' else a[0,1,2]-a[0,1,3])
    actual=np.array(actual);err=abs(signed-actual);scaled=err/np.maximum(absolute,1e-300);assert np.max(scaled)<2e-9,(actual,signed,scaled)
    report=dict(kind=kind,identity=json.loads(identity),stage_dot_checks=test(),signed=signed.tolist(),absolute=absolute.tolist(),actual=actual.tolist(),max_scaled_error=float(scaled.max()),source_steps=np.flatnonzero(np.any(terms!=0,axis=(1,2,3))).tolist(),signed_by_stage=terms.sum(axis=0).tolist(),absolute_by_stage=abs(terms).sum(axis=0).tolist(),checkpoint_sha256=hashlib.sha256(p.read_bytes()).hexdigest(),scope='actual original common A-grid finite source contraction, not a continuum bias, not interval propagation')
    (work/(kind+'.dual.json')).write_text(json.dumps(report,indent=2)+'\n');return 0

if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('kind',choices=('gap','parity_sms'));p.add_argument('--work',type=Path,default=Path('.local-f8-common'));p.add_argument('--budget',type=float,default=12.);a=p.parse_args();assert 0<a.budget<=90;raise SystemExit(run(a.work,a.kind,a.budget))
