"""Receipt-anchored diagnostic continuation; not D3.5 anchors."""
import argparse,hashlib,json,math,os,time
from pathlib import Path
import numpy as np
from scipy.optimize import brentq
from ksw668_f8_tt_multipole import F
from ksw668_f8_fv_source_flux import exact_cell_averages
from ksw668_f8_signed_route_stage import step

ANCHORS={('ledger',378,337):'baaafd747a426709fb58d53663a8b2cde11c946f30aafe049d138c1f484cf796',('ledger',503,449):'fa7e7119451f1b6f103ba614ee47eb53da4522c5a2d500805522353f8e72a27d',('paired',378,337):'b468bbefd2f2f63e88c5a687fb086cd31b1db557fd8d465b57a4e92499e1f84e',('paired',503,449):'f79890aafa7214c7f022dfd0c09a738e30a18b719dae8bf00302697e74c1e1f0'}
def digest(x):return hashlib.sha256(np.ascontiguousarray(x).tobytes()).hexdigest()
def run(a):
    dr,dy,nr,ny=(.008,.012,378,337) if a.grid=='medium' else (.006,.009,503,449)
    T0=F(1);span=F(12)-T0;nt=math.ceil(span/.0006);h=span/nt
    if not 110<a.target<=nt+1 or not 0<a.budget<=75:raise ValueError('bounded continuation only')
    prefix=a.work/f'{a.route}-{nr}-{ny}-prefix.npz';path=a.work/f'{a.route}-{nr}-{ny}-postsource.npz'
    with np.load(prefix,allow_pickle=False) as z:X=z['X'];k=int(z['k'])
    anchor=ANCHORS[a.route,nr,ny]
    if k!=110 or digest(X)!=anchor:raise ValueError('prefix receipt mismatch')
    src=exact_cell_averages(.04,np.arange(nr)*dr,dr);cp=np.zeros_like(src);cm=cp.copy()
    for q,d in enumerate((3,7,11)):
        for j in range(1,nr):
            den=(j+.5)**d-(j-.5)**d;cp[q,j]=d*(j+.5)**(d-1)/den;cm[q,j]=d*(j-.5)**(d-1)/den
    files=['ksw668_f8_tt_multipole.py','ksw668_f8_fv_source_flux.py','ksw668_f8_signed_route_stage.py','ksw668_f8_weighted_normal_stage.py',Path(__file__).name]
    ident=json.dumps(dict(anchor=anchor,route=a.route,grid=[nr,ny],h=h,nt=nt,source=digest(src),coefficients=[digest(cp),digest(cm)],files={p:hashlib.sha256(Path(__file__).with_name(p).read_bytes()).hexdigest() for p in files},numpy=np.__version__),sort_keys=True)
    if path.exists():
        with np.load(path,allow_pickle=False) as z:
            if z['identity'].item()!=ident:raise ValueError('continuation identity mismatch')
            X=z['X'];k=int(z['k'])
            if digest(X)!=z['sha'].item():raise ValueError('continuation digest mismatch')
    if X.shape!=(6,3,ny,nr) or not 110<=k<=a.target:raise ValueError('continuation shape/cursor')
    def coeff(T):
        t=brentq(lambda t:F(t)-T,.5,25);v=-1/math.sqrt(1+t*t);q=2*(T-T0)/.065-1
        amp=-6*math.sqrt(1-v*v)*t*math.exp(1-1/(1-q*q)) if abs(q)<1 else 0.
        if amp!=0:raise ValueError('postsource clock is active')
        return v,1/t,amp
    def validate(X):
        if not np.isfinite(X).all() or np.any(X[..., -1]) or np.any(X[4,:,1:]) or np.any(X[5,:,:-1]):raise ValueError('carrier integrity')
        U,P,M,R,J,K=X;D=np.empty_like(U);D[:,0]=(U[:,1]-U[:,0])/dy;D[:,-1]=(U[:,-1]-U[:,-2])/dy;D[:,1:-1]=(U[:,2:]-U[:,:-2])/(2*dy)
        q=(P-M)/2-D-R-J-K;scale=max(1.,*(np.max(abs(x)) for x in (P,M,D,R,J,K)))
        err=float(np.max(abs(q))/scale)
        if err>1e-10:raise ValueError('signed constraint')
        return err
    initial=k;start=time.monotonic();worst=validate(X)
    while k<a.target:
        X=step(X,T0+k*h,h,coeff,dr,dy,src,cp,cm,a.route);k+=1
        if k%16==0 or k==a.target or time.monotonic()-start>=a.budget:
            worst=max(worst,validate(X));sha=digest(X);tmp=path.with_suffix('.tmp')
            with tmp.open('wb') as f:np.savez(f,X=X,k=k,identity=ident,sha=sha);f.flush();os.fsync(f.fileno())
            os.replace(tmp,path)
            with np.load(path,allow_pickle=False) as z:
                if int(z['k'])!=k or z['identity'].item()!=ident or digest(z['X'])!=sha:raise ValueError('checkpoint readback')
            if time.monotonic()-start>=a.budget:break
    return dict(route=a.route,grid=a.grid,nr=nr,ny=ny,initial=initial,cursor=k,target=a.target,nt=nt,elapsed_T=k*h,physical_t=brentq(lambda t:F(t)-T0-k*h,.5,25),max_scaled_constraint=worst,max_state=float(np.max(abs(X))),sha256=digest(X),seconds=time.monotonic()-start,identity=json.loads(ident),full_clock=k==nt+1)
if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('work',type=Path);p.add_argument('--route',choices=['paired','ledger'],required=True);p.add_argument('--grid',choices=['medium','fine'],required=True);p.add_argument('--target',type=int,default=4517);p.add_argument('--budget',type=float,default=60);a=p.parse_args();print(json.dumps(run(a)),flush=True)
