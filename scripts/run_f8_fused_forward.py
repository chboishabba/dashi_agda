"""Bounded receipt-anchored full-clock fused forward; independent consumers.
Not D3.5 paired checkpoint anchors or reverse attribution.
"""
import argparse,hashlib,json,math,os,time
from pathlib import Path
import numpy as np
from scipy.optimize import brentq
from ksw668_f8_tt_multipole import F
from ksw668_f8_fv_source_flux import exact_cell_averages
from ksw668_f8_signed_route_stage import step
from f8_fused_step import step_into
from warp_native_geometric_receiver import receiver_bank
from check_f8_signed_window import window_rows
from check_f8_shrinking_injection import build,read

ANCHORS={('ledger',378,337):'72431a0df628ab96bdd7dc4b04bf13a150c6dadc9ceee9dfc8a2cfef38cb1235',('paired',378,337):'ba9a4b581e204ff325832524ab5cdf44acd8680b4ea61447917a467a1785143d',('ledger',503,449):'ef331e84476834a17e648998042034d24300817f5e03dcccc611c0134500d5ec',('paired',503,449):'2b3f7e756bcb51418f60e4cf17e0fe05399f839e3439d37f76e945641e7486e0'}
def digest(x):return hashlib.sha256(np.ascontiguousarray(x).tobytes()).hexdigest()
def run(a):
    dr,dy,nr,ny=(.008,.012,378,337) if a.grid=='medium' else (.006,.009,503,449)
    T0=F(1);span=F(12)-T0;nt=math.ceil(span/.0006);h=span/nt;end=nt+1
    if not 0<a.budget<=75:raise ValueError('bounded budget')
    key=f'{a.route}-{nr}-{ny}';path=a.work/f'{key}-fused.npz'
    with np.load(a.work/f'{key}-postsource.npz',allow_pickle=False) as z:X=z['X'];k=int(z['k'])
    anchor=ANCHORS[a.route,nr,ny]
    if k!=200 or digest(X)!=anchor:raise ValueError('step200 receipt mismatch')
    src=exact_cell_averages(.04,np.arange(nr)*dr,dr);cp=np.zeros_like(src);cm=cp.copy()
    for q,d in enumerate((3,7,11)):
        for j in range(1,nr):
            den=(j+.5)**d-(j-.5)**d;cp[q,j]=d*(j+.5)**(d-1)/den;cm[q,j]=d*(j-.5)**(d-1)/den
    def coeff(T):
        t=brentq(lambda t:F(t)-T,.5,25);v=-1/math.sqrt(1+t*t);q=2*(T-T0)/.065-1
        amp=-6*math.sqrt(1-v*v)*t*math.exp(1-1/(1-q*q)) if abs(q)<1 else 0.
        return v,1/t,amp
    Tgrid=np.arange(end+1)*h;ts=np.array([1/coeff(T0+n*h)[1] for n in range(end+1)])
    vel=np.array([coeff(T0+n*h/2)[0] for n in range(2*end+1)])
    bulk=math.sqrt(span**2-(1-1/12)**2);rxs=(bulk-.012,bulk+.1);delta=.06
    patches=[build(Tgrid,ts,dy,ny,dr,nr,rx,delta) for rx in rxs]
    windows=[window_rows(ts,h,rx,.04,dr,nr,span-.15,.10)[:2] for rx in rxs]
    banks=[receiver_bank(12,rx,.04,dr,dy,h,vel,nt,nr,3) for rx in rxs]
    assert all(not np.any(src[:,p[2]]) and p[0].start>200 for p in patches)
    assert all(not np.any(src[:,i]) and not np.any(w[:,:201]) for i,w in windows)
    names=['ksw668_f8_tt_multipole.py','ksw668_f8_fv_source_flux.py','ksw668_f8_signed_route_stage.py','ksw668_f8_weighted_normal_stage.py','f8_fused_step.py','warp_native_geometric_receiver.py','check_f8_signed_window.py','check_f8_shrinking_jet.py','check_f8_shrinking_injection.py',Path(__file__).name]
    ident=json.dumps(dict(anchor=anchor,route=a.route,grid=[nr,ny],h=h,nt=nt,source=digest(src),cp=digest(cp),cm=digest(cm),delta=delta,files={p:hashlib.sha256(Path(__file__).with_name(p).read_bytes()).hexdigest() for p in names},numpy=np.__version__),sort_keys=True)
    raw=np.zeros((2,6,3));window=np.zeros((2,2,3));shrink=np.zeros_like(raw)
    if path.exists():
        with np.load(path,allow_pickle=False) as z:
            if z['identity'].item()!=ident:raise ValueError('continuation identity')
            X=z['X'];k=int(z['k']);raw=z['raw'];window=z['window'];shrink=z['shrink']
            for name,data in [('X',X),('raw',raw),('window',window),('shrink',shrink)]:
                if digest(data)!=z[name+'_sha'].item():raise ValueError('continuation digest')
    if X.shape!=(6,3,ny,nr) or not 200<=k<=end:raise ValueError('carrier/cursor')
    def validate(X):
        if not np.isfinite(X).all() or np.any(X[..., -1]) or np.any(X[4,:,1:]) or np.any(X[5,:,:-1]):raise ValueError('carrier integrity')
        U,P,M,R,J,K=X;D=np.empty_like(U);D[:,0]=(U[:,1]-U[:,0])/dy;D[:,-1]=(U[:,-1]-U[:,-2])/dy;D[:,1:-1]=(U[:,2:]-U[:,:-2])/(2*dy)
        q=(P-M)/2-D-R-J-K;err=float(np.max(abs(q))/max(1.,*(np.max(abs(x)) for x in (P,M,D,R,J,K))))
        if err>1e-10:raise ValueError('signed constraint')
        return err
    def observe(n,X):
        for pos,(p,(idx,w),bank) in enumerate(zip(patches,windows,banks)):
            if p[0].start<=n<p[0].stop:
                for ch in range(6):shrink[pos,ch]+=read(p,ch,n,X)
            if np.any(w[:,n]):window[pos]+=np.sum(w[:,n]*X[0,:,0,:][:,idx],axis=-1)
            if nt-1<=n<=end:raw[pos]+=np.einsum('ciqyr,iqyr->cq',bank[:,n-nt+1],X[:3,:,:3,:])
    start=time.monotonic();initial=k;worst=validate(X);out,A,B=[np.empty_like(X) for _ in range(3)]
    if k<end:
        # Actual receipt-state control, not just arbitrary-state parity.
        ref=step(X,T0+k*h,h,coeff,dr,dy,src,cp,cm,a.route)
        step_into(X,out,A,B,T0+k*h,h,coeff,dr,dy,src,cp,cm,a.route)
        if not np.array_equal(ref,out):raise ValueError('receipt-state fused parity')
        del ref
    # Persist observations already consumed through k, inclusive; all are zero at anchor.
    while k<end:
        step_into(X,out,A,B,T0+k*h,h,coeff,dr,dy,src,cp,cm,a.route);X,out=out,X;k+=1
        observe(k,X)
        if k%128==0 or k==end or time.monotonic()-start>=a.budget:
            worst=max(worst,validate(X));arrays=dict(X=X,raw=raw,window=window,shrink=shrink);sha={p+'_sha':digest(v) for p,v in arrays.items()}
            tmp=path.with_suffix('.tmp')
            with tmp.open('wb') as f:np.savez(f,identity=ident,k=k,**arrays,**sha);f.flush();os.fsync(f.fileno())
            os.replace(tmp,path)
            with np.load(path,allow_pickle=False) as z:
                if int(z['k'])!=k or z['identity'].item()!=ident or any(digest(z[p])!=v for p,v in ((name,sha[name+'_sha']) for name in arrays)):raise ValueError('readback')
            if time.monotonic()-start>=a.budget:break
    return dict(route=a.route,grid=a.grid,initial=initial,cursor=k,end=end,physical_t=float(ts[k]),seconds=time.monotonic()-start,max_scaled_constraint=worst,sha256=digest(X),complete=k==end,rx=rxs,delta=delta,raw=raw.tolist(),window=window.tolist(),shrink=shrink.tolist())

if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('work',type=Path);p.add_argument('--route',choices=['ledger','paired'],required=True);p.add_argument('--grid',choices=['medium','fine'],required=True);p.add_argument('--budget',type=float,default=15);print(json.dumps(run(p.parse_args())),flush=True)
