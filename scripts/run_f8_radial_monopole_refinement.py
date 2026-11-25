"""Original compact TT monopole, independent radial refinement at fixed dy and clock.
All six forward channels; original source and observation operators; local only.
"""
import argparse,hashlib,json,math,os,time
from fractions import Fraction as Fq
from pathlib import Path
import numpy as np
from scipy.optimize import brentq
from ksw668_f8_tt_multipole import F
from ksw668_f8_fv_source_flux import exact_cell_averages
from ksw668_f8_signed_route_stage import step
from f8_fused_step import step_into
from run_f8_fused_forward import digest
from warp_native_geometric_receiver import receiver_bank
from check_f8_signed_window import window_rows
from check_f8_shrinking_injection import build


def radial_cap(n,h):
    # Exact d=3 restriction of check_f8_modal_cfl.radial_upper and envelope.
    p=[Fq(6)];m=[Fq(0)]
    for j in range(1,n):
        a,b=Fq(2*j-1,2),Fq(2*j+1,2);den=b**3-a**3
        p.append(3*b*b/den);m.append(3*a*a/den)
    def up(x,scale):return Fq(math.isqrt(x.numerator*scale**2//x.denominator)+1,scale)
    off=[Fq(0)]+[up(p[j]*m[j+1],10**9) for j in range(n-1)]+[Fq(0)]
    lam=max(p[j]+m[j]+off[j]+off[j+1] for j in range(n))/Fq(str(h))**2
    cap=up(lam,10**6)+Fq(81,16)/Fq('.009')+24+Fq(3,2)
    return float(lam),float(Fq(9,10)/cap)


def run(a):
    dr=float(a.dr);dy=.009;ny=449;nr=int(Fq('3.012')/Fq(a.dr))+1
    assert Fq(a.dr)*(nr-1)==Fq('3.012') and 0<a.budget<=75
    T0=F(1);span=F(12)-T0;nt=math.ceil(span/.0006);h=span/nt;end=nt+1
    lam,safe=radial_cap(nr-1,dr);assert h<=safe
    src=exact_cell_averages(.04,np.arange(nr)*dr,dr)[:1].copy();cp=np.zeros_like(src);cm=cp.copy()
    for j in range(1,nr):
        den=(j+.5)**3-(j-.5)**3;cp[0,j]=3*(j+.5)**2/den;cm[0,j]=3*(j-.5)**2/den
    def coeff(T):
        t=brentq(lambda t:F(t)-T,.5,25);v=-1/math.sqrt(1+t*t);q=2*(T-T0)/.065-1
        return v,1/t,-6*math.sqrt(1-v*v)*t*math.exp(1-1/(1-q*q)) if abs(q)<1 else 0.
    T=np.arange(end+1)*h;ts=np.array([1/coeff(T0+n*h)[1] for n in range(end+1)])
    vel=np.array([coeff(T0+i*h/2)[0] for i in range(2*end+1)])
    bulk=math.sqrt(span**2-(1-1/12)**2);rx=(bulk-.012,bulk+.1);delta=.06
    obs=[(build(T,ts,dy,ny,dr,nr,r,delta),window_rows(ts,h,r,.04,dr,nr,span-.15,.10)[:2],receiver_bank(12,r,.04,dr,dy,h,vel,nt,nr,3)) for r in rx]
    assert all(not np.any(src[:,p[2]]) and not np.any(src[:,i]) for p,(i,w),bank in obs)
    names=['ksw668_f8_tt_multipole.py','ksw668_f8_fv_source_flux.py','ksw668_f8_signed_route_stage.py','ksw668_f8_weighted_normal_stage.py','f8_fused_step.py','warp_native_geometric_receiver.py','check_f8_signed_window.py','check_f8_shrinking_jet.py','check_f8_shrinking_injection.py',Path(__file__).name]
    ident=json.dumps(dict(grid=[nr,ny],dr=dr,dy=dy,h=h,nt=nt,source=digest(src),cp=digest(cp),cm=digest(cm),delta=delta,files={p:hashlib.sha256(Path(__file__).with_name(p).read_bytes()).hexdigest() for p in names},numpy=np.__version__),sort_keys=True)
    X=np.zeros((6,1,ny,nr));k=0;raw=np.zeros((2,6));window=np.zeros((2,2));shrink=np.zeros_like(raw);worst=0.
    path=a.work/f'ledger-radial-{a.dr}-mono.npz'
    if path.exists():
        with np.load(path,allow_pickle=False) as z:
            assert z['identity'].item()==ident;X=z['X'];k=int(z['k']);raw=z['raw'];window=z['window'];shrink=z['shrink'];worst=float(z['worst'])
            assert all(digest(v)==z[n+'_sha'].item() for n,v in dict(X=X,raw=raw,window=window,shrink=shrink,worst=np.array(worst)).items())
    assert X.shape==(6,1,ny,nr) and 0<=k<=end
    out,A,B=[np.empty_like(X) for _ in range(3)];start=time.monotonic();initial=k
    if k<end:
        Z=np.zeros((6,3,ny,nr));Z[:,:1]=X;src3=np.zeros((3,nr));src3[:1]=src;cp3=np.zeros_like(src3);cm3=cp3.copy();cp3[:1]=cp;cm3[:1]=cm
        ref=step(Z,T0+k*h,h,coeff,dr,dy,src3,cp3,cm3,'ledger');step_into(X,out,A,B,T0+k*h,h,coeff,dr,dy,src,cp,cm,'ledger')
        assert np.array_equal(ref[:,:1],out) and not np.any(ref[:,1:]);del Z,ref
    while k<end:
        step_into(X,out,A,B,T0+k*h,h,coeff,dr,dy,src,cp,cm,'ledger');X,out=out,X;k+=1
        for pos,(p,(idx,w),bank) in enumerate(obs):
            tt,yy,rr,o=p
            if tt.start<=k<tt.stop:shrink[pos]+=np.sum(o[:,0,k-tt.start]*X[0,0,yy,rr],axis=(1,2))
            if np.any(w[:,k]):window[pos]+=np.sum(w[:,k,0]*X[0,0,0,idx],axis=-1)
            if nt-1<=k<=end:raw[pos]+=np.einsum('ciyr,iyr->c',bank[:,k-nt+1,:,0],X[:3,0,:3,:])
        if k%128==0 or k==end or time.monotonic()-start>=a.budget:
            assert np.isfinite(X).all() and not np.any(X[..., -1]) and not np.any(X[4,:,1:]) and not np.any(X[5,:,:-1])
            U,P,M,R,J,K=X;D=np.empty_like(U);D[:,0]=(U[:,1]-U[:,0])/dy;D[:,-1]=(U[:,-1]-U[:,-2])/dy;D[:,1:-1]=(U[:,2:]-U[:,:-2])/(2*dy)
            err=float(np.max(abs((P-M)/2-D-R-J-K))/max(1.,*(np.max(abs(x)) for x in (P,M,D,R,J,K))));assert err<1e-10;worst=max(worst,err)
            arrays=dict(X=X,raw=raw,window=window,shrink=shrink,worst=np.array(worst));sha={n+'_sha':digest(v) for n,v in arrays.items()};tmp=path.with_suffix('.tmp')
            with tmp.open('wb') as f:np.savez(f,identity=ident,k=k,**arrays,**sha);f.flush();os.fsync(f.fileno())
            os.replace(tmp,path)
            with np.load(path,allow_pickle=False) as z:assert int(z['k'])==k and z['identity'].item()==ident and all(digest(z[n])==sha[n+'_sha'].item() for n in arrays)
            if time.monotonic()-start>=a.budget:break
    return dict(dr=dr,dy=dy,nr=nr,ny=ny,initial=initial,cursor=k,end=end,h=h,lambda_upper=lam,safe_dt=safe,physical_t=float(ts[k]),constraint=worst,sha256=digest(X),raw=raw.tolist(),window=window.tolist(),shrink=shrink.tolist(),seconds=time.monotonic()-start)

if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('work',type=Path);p.add_argument('--dr',default='.004');p.add_argument('--budget',type=float,default=12);print(json.dumps(run(p.parse_args())),flush=True)
