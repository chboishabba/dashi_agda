"""Common scalar prepotential on original enlarged box; exact Bessel reconstruction.
Finite modal weighted4 ledger evolution, not native FV equivalence or convergence.
"""
import argparse,json,math,time,hashlib,os
from pathlib import Path
import numpy as np
from scipy.special import spherical_jn
from scipy.optimize import brentq
from numpy.polynomial.legendre import leggauss
from numba import njit,prange
from f8_fused_step import combine,weights
from ksw668_f8_tt_multipole import F
from ksw668_f8_weighted_normal_stage import weighted_stage4
from warp_native_geometric_receiver import rows
from check_f8_signed_window import window_rows
from run_f8_fused_forward import digest

@njit(cache=True,parallel=True)
def stage(X,base,out,h,stage_id,dy,v,amp,src,lam,z,lo,hi):
    _,ny,n=X.shape
    for i in prange(ny):
        zi=z[i];wl=(zi/z[i-1])**1.5 if i else 0.;wh=(zi/z[i+1])**1.5 if i<ny-1 else 0.
        for j in range(n):
            u,p,m=X[0,i,j],X[1,i,j],X[2,i,j];w=((1+v)*p+(1-v)*m)/2;N=(p-m)/2
            force=-lam[j]*u-3*N/zi;cw=1.5*w/zi
            if i:
                pl,ml=X[1,i-1,j],X[2,i-1,j];cw+=lo[i]*((1+v)*pl+(1-v)*ml)/2
            if i<ny-1:
                ph,mh=X[1,i+1,j],X[2,i+1,j];cw+=hi[i]*((1+v)*ph+(1-v)*mh)/2
            if i==0:dp=(wh*ph-p)/dy+1.5*p/zi;dm=(wh*mh-m)/dy+1.5*m/zi
            elif i==ny-1:dp=(p-wl*pl)/dy+1.5*p/zi;dm=(m-wl*ml)/dy+1.5*m/zi
            else:dp=(wh*ph-wl*pl)/(2*dy)+1.5*p/zi;dm=(wh*mh-wl*ml)/(2*dy)+1.5*m/zi
            rp=(1+v)*dp+force;rm=(v-1)*dm+force;rj=0.;rk=0.
            if i==ny-1:rp-=2*(1+v)*p/dy;rk=-(1+v)*p/dy
            if i==0:
                target=(2*amp*src[j]-(1+v)*p)/(v-1);rm+=2*(1-v)*(target-m)/dy
                rj=-2*(((1+v)*p+(v-1)*m)/2-amp*src[j])/dy
            for c,val in enumerate((w,rp,rm,cw,rj,rk)):out[c,i,j]=combine(X[c,i,j],base[c,i,j],val,h,stage_id)

def check():
    # Independent exact same finite FV eigenbasis stage comparison.
    n,ny,dr,dy=7,9,.04,.03;r=np.arange(n)*dr;a=np.maximum(0,r-dr/2);b=r+dr/2;vol=(b**3-a**3)/3
    p=b*b/(vol*dr);m=a*a/(vol*dr);S=np.diag(p+m)+np.diag(-np.sqrt(p[:-1]*m[1:]),1)+np.diag(-np.sqrt(p[:-1]*m[1:]),-1)
    lam,V=np.linalg.eigh(S);B=V/np.sqrt(vol)[:,None];rng=np.random.default_rng(1547);X=rng.normal(size=(6,ny,n));src=rng.normal(size=n);out=np.empty_like(X);worst=0.
    cp=np.zeros((3,n+1));cm=cp.copy();cp[0,:n]=p*dr**2;cm[0,:n]=m*dr**2
    U=np.zeros((3,3,ny,n+1));U[:,0,:,:n]=X[:3]@B.T;rhs=np.empty_like(U);g=np.zeros((3,n+1));g[0,:n]=B@src
    for t in (1.,2.,12.):
        v=-1/math.sqrt(1+t*t);z,lo,hi,*_=weights(1/t,dy,ny);h=.0001
        stage(X,X,out,h,0,dy,v,.23,src,lam,z,lo,hi)
        weighted_stage4(*U,*rhs,dr,dy,1/t,v,.23,g,cp,cm,4)
        ref=(U+h*rhs)[:,0,:,:n];test=out[:3]@B.T
        err=float(np.max(abs(test-ref))/max(1.,np.max(abs(ref))));assert err<1e-12;worst=max(worst,err)
    return dict(stage_checks=3,max_scaled=worst)

def run(a):
    R,Y,eps=3.012,4.032,.04;dy=Y/(a.ny-1);n=a.modes;ny=a.ny;k=np.arange(1,n+1)*np.pi/R;lam=k*k
    T0=F(1);span=F(12)-T0;nt=math.ceil(span/a.dt);h=span/nt;end=nt+1
    safe=.9/(k[-1]+81/(16*dy)+25.5);assert h<=safe and dy<=1/48
    def source(nq):
        x,w=leggauss(nq);r=eps*(1+x)/2;return math.sqrt(2/R)*eps**4*(np.sin(k[:,None]*r)@(w*r*np.exp(1-1/(1-(r/eps)**2))*eps/2))
    src=source(256);ref=source(512);qerr=float(np.max(abs(src-ref)));assert qerr<1e-12*max(abs(ref));src=ref
    def coeff(T):
        t=brentq(lambda t:F(t)-T,.5,25);v=-1/math.sqrt(1+t*t);q=2*(T-T0)/.065-1
        return v,1/t,-6*math.sqrt(1-v*v)*t*math.exp(1-1/(1-q*q)) if abs(q)<1 else 0.
    ts=np.array([1/coeff(T0+i*h)[1] for i in range(end+1)]);rx=np.array([math.sqrt(span**2-(1-1/12)**2)-.012,math.sqrt(span**2-(1-1/12)**2)+.1]);B=[];Brr=[]
    for r in rx:
        f=[];d=[]
        for l,c in ((0,.4),(2,-4/7),(4,1/35)):
            x=k*r;j=spherical_jn(l,x);jp=spherical_jn(l,x,True);fac=math.sqrt(2/R)*k**5*c
            f.append(fac*j);d.append(fac*lam*(-2*jp/x-(1-l*(l+1)/x**2)*j))
        B.append(f);Brr.append(d)
    B=np.array(B);Brr=np.array(Brr);L=-B*lam
    _,_,coef,_,_=window_rows(ts,h,rx[0],eps,.006,503,span-.15,.10);P=[];C=[]
    for a2,a1,a0 in coef:
        p=np.zeros(end+1);p[:-2]+=a2[1:-1]/h**2-a1[1:-1]/(2*h);p[1:-1]-=2*a2[1:-1]/h**2;p[2:]+=a2[1:-1]/h**2+a1[1:-1]/(2*h);P.append(h*p);C.append(h*a0)
    P=np.array(P);C=np.array(C);X=np.zeros((6,ny,n));raw=np.zeros((2,6,3,n));win=np.zeros((2,2,3,n));snap=np.zeros((3,3,3,n));cursor=0;worst=0.
    path=a.work/f'common-modal-{n}-{ny}-{a.dt}.npz';identity=json.dumps(dict(n=n,ny=ny,h=h,source=digest(src),code=hashlib.sha256(Path(__file__).read_bytes()).hexdigest()),sort_keys=True)
    if path.exists():
        with np.load(path,allow_pickle=False) as z:
            assert z['identity'].item()==identity;cursor=int(z['cursor']);X=z['X'];win=z['win'];snap=z['snap'];worst=float(z['worst'])
            assert all(digest(v)==z[key+'_sha'].item() for key,v in dict(X=X,win=win,snap=snap,worst=np.array(worst)).items())
    out,A,D=[np.empty_like(X) for _ in range(3)];start=time.monotonic();initial=cursor
    while cursor<end:
        T=T0+cursor*h
        for q,(inp,dst,t) in enumerate(((X,A,T),(A,D,T+h),(D,out,T+h/2))):
            v,b,amp=coeff(t);z,lo,hi,*_=weights(b,dy,ny);stage(inp,X,dst,h,q,dy,v,amp,src,lam,z,lo,hi)
        X,out=out,X;cursor+=1
        if np.any(P[:,cursor]) or np.any(C[:,cursor]):win+=(P[:,cursor][None,:,None,None]*B[:,None]+C[:,cursor][None,:,None,None]*L[:,None])*X[0,0]
        if nt-1<=cursor<=end:snap[cursor-nt+1]=X[:3,:3]
        if cursor%128==0 or cursor==end or time.monotonic()-start>=a.budget:
            U,pp,mm,rr,jj,kk=X;DU=np.empty_like(U);DU[0]=(U[1]-U[0])/dy;DU[-1]=(U[-1]-U[-2])/dy;DU[1:-1]=(U[2:]-U[:-2])/(2*dy)
            err=float(np.max(abs((pp-mm)/2-DU-rr-jj-kk))/max(1e-300,*(np.max(abs(x)) for x in (pp,mm,DU,rr,jj,kk))));worst=max(worst,err);assert np.isfinite(X).all() and err<1e-8
            arrays=dict(X=X,win=win,snap=snap,worst=np.array(worst));sha={key+'_sha':digest(v) for key,v in arrays.items()};tmp=path.with_suffix('.tmp')
            with tmp.open('wb') as f:np.savez(f,identity=identity,cursor=cursor,**arrays,**sha);f.flush();os.fsync(f.fileno())
            os.replace(tmp,path)
            with np.load(path,allow_pickle=False) as z:assert int(z['cursor'])==cursor and all(digest(z[key])==sha[key+'_sha'] for key in arrays)
            if time.monotonic()-start>=a.budget:break
    result=dict(modes=n,ny=ny,dy=dy,dt=h,safe_dt=safe,initial=initial,cursor=cursor,end=end,source_quadrature_error=qerr,max_constraint=worst,state_sha=digest(X),seconds=time.monotonic()-start)
    if cursor==end:
        v=-1/np.sqrt(1+ts[nt-1:nt+2]**2);U=snap[:,0];W=((1+v[:,None,None])*snap[:,1]+(1-v[:,None,None])*snap[:,2])/2;d=np.array([-3,4,-1])/(2*dy);d2=np.array([1,-2,1])/dy**2
        jets=np.stack([B*W[1,0],B*(W[2,0]-W[0,0])/(2*h),B*(d@U[1]),B*(d@W[1]),B*(d2@U[1]),L*U[1,0],Brr*U[1,0]])
        raw=np.einsum('cj,jpqn->pcqn',rows(12),jets);assert np.max(abs(raw[:,2]-raw[:,3]+(1/12+1/(2*12**3))*raw[:,4]+raw[:,5]/(3*12**2)))<1e-8
        result.update(cuts=[dict(n=i,raw=raw[...,:i].sum(-1).tolist(),window=win[...,:i].sum(-1).tolist(),raw_abs=abs(raw[...,:i]).sum(-1).tolist(),window_abs=abs(win[...,:i]).sum(-1).tolist()) for i in sorted(set([min(n,j) for j in (32,64,128,256,512,n)]))]);np.savez(a.work/f'common-modal-{n}-{ny}-{a.dt}-observations.npz',raw=raw,window=win,source=src,k=k)
    return result

if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('work',type=Path);p.add_argument('--modes',type=int,default=512);p.add_argument('--ny',type=int,default=225);p.add_argument('--dt',type=float,default=.0006);p.add_argument('--budget',type=float,default=12);p.add_argument('--check',action='store_true');a=p.parse_args();assert 0<a.budget<=75;print(json.dumps(check() if a.check else run(a)),flush=True)
