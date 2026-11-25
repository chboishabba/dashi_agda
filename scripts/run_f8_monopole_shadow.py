"""D3.5 aggregate monopole attribution, not per-step/channel reverse budget.
Original LVII exact shell map, D3.4 normal nodal map, original observer rows.
Only l=0 evolves (independent multipoles); histories retained. Local only.
"""
import argparse, hashlib, json, math, os, time
from pathlib import Path
import numpy as np
import sympy as s
from scipy.sparse import csr_matrix
from scipy.optimize import brentq
from ksw668_f8_tt_multipole import F
from ksw668_f8_fv_source_flux import exact_cell_averages
from ksw668_f8_signed_route_stage import step
from f8_fused_step import step_into
from run_f8_fused_forward import ANCHORS,digest
from warp_native_geometric_receiver import receiver_bank
from check_f8_signed_window import window_rows
from check_f8_shrinking_injection import build


def maps():
    # LVII overlap (d=3), exact shell measures; zero extension at outer closure.
    hc,hf=s.Rational('.008'),s.Rational('.006')
    C,Fc=[[(max(0,(j-s.Rational(1,2))*h),(j+s.Rational(1,2))*h) for j in range(n)] for h,n in ((hc,377),(hf,502))]
    mass=lambda a,b:(b**3-a**3)/3
    wc=[mass(*q) for q in C];wf=[mass(*q) for q in Fc];entries=[];i=j=0
    while i<len(Fc) and j<len(C):
        a,b=max(Fc[i][0],C[j][0]),min(Fc[i][1],C[j][1])
        if b>a:entries.append((i,j,mass(a,b)))
        if Fc[i][1]<=C[j][1]:i+=1
        else:j+=1
    rs=[s.S.Zero]*502;cs=[s.S.Zero]*377
    for i,j,v in entries:rs[i]+=v;cs[j]+=v
    assert all(0<=a<=b for a,b in zip(rs,wf)) and all(0<=a<=b for a,b in zip(cs,wc))
    assert sum(rs)==sum(cs)==mass(s.S.Zero,min(C[-1][1],Fc[-1][1]))
    assert all(wf[i]*(v/wf[i])==wc[j]*(v/wc[j]) for i,j,v in entries)
    I=csr_matrix(([float(v/wf[i]) for i,j,v in entries],([i for i,j,v in entries],[j for i,j,v in entries])),shape=(502,377))
    # Exact normal endpoints, as in D3.4; sparse equivalent of Y.
    yrows=[];ycols=[];ys=[]
    for i in range(449):
        x=s.Rational(3*i,4);j=min(int(x),335);a=float(x-j)
        yrows.extend([i,i]);ycols.extend([j,j+1]);ys.extend([1-a,a])
    Y=csr_matrix((ys,(yrows,ycols)),shape=(449,337))
    return I,Y,np.array(wc,float),np.array(wf,float)


def run(a):
    I,Y,wc,wf=maps();sc=exact_cell_averages(.04,np.arange(378)*.008,.008);sf=exact_cell_averages(.04,np.arange(503)*.006,.006)
    sm=np.zeros((1,503));sm[0,:-1]=I@sc[0,:-1]
    assert abs(wf@sm[0,:-1]-wc@sc[0,:-1])<1e-12
    dr,dy,nr,ny=(.006,.009,503,449) if a.kind=='shadow' else (.008,.012,378,337)
    src=sm if a.kind=='shadow' else sc[:1].copy()
    cp=np.zeros_like(src);cm=cp.copy()
    for j in range(1,nr):
        den=(j+.5)**3-(j-.5)**3;cp[0,j]=3*(j+.5)**2/den;cm[0,j]=3*(j-.5)**2/den
    T0=F(1);span=F(12)-T0;nt=math.ceil(span/.0006);h=span/nt;end=nt+1
    def coeff(T):
        t=brentq(lambda t:F(t)-T,.5,25);v=-1/math.sqrt(1+t*t);q=2*(T-T0)/.065-1
        return v,1/t,-6*math.sqrt(1-v*v)*t*math.exp(1-1/(1-q*q)) if abs(q)<1 else 0.
    T=np.arange(end+1)*h;ts=np.array([1/coeff(T0+x)[1] for x in T]);vel=np.array([coeff(T0+i*h/2)[0] for i in range(2*end+1)])
    bulk=math.sqrt(span**2-(1-1/12)**2);rx=(bulk-.012,bulk+.1)
    def obs_setup(dr,dy,nr,ny):
        return [(build(T,ts,dy,ny,dr,nr,r,.06),window_rows(ts,h,r,.04,dr,nr,span-.15,.10)[:2],receiver_bank(12,r,.04,dr,dy,h,vel,nt,nr,3)) for r in rx]
    fine_obs=obs_setup(.006,.009,503,449);coarse_obs=obs_setup(dr,dy,nr,ny) if a.kind=='coarse' else None
    keys=('raw','window','shrink');shapes=((2,6),(2,2),(2,6));vals={k:np.zeros(z) for k,z in zip(keys,shapes)};own={k:np.zeros(z) for k,z in zip(keys,shapes)}
    X=np.zeros((6,1,ny,nr));k=0;anchor='zero';path=a.work/f'{a.route}-monopole-{a.kind}.npz'
    if a.kind=='coarse':
        with np.load(a.work/f'{a.route}-378-337-postsource.npz',allow_pickle=False) as z:
            assert int(z['k'])==200 and digest(z['X'])==ANCHORS[a.route,378,337];X=z['X'][:,:1].copy();k=200;anchor=ANCHORS[a.route,378,337]
    names=['run_f8_monopole_shadow.py','f8_fused_step.py','run_f8_fused_forward.py','ksw668_f8_tt_multipole.py','ksw668_f8_fv_source_flux.py','ksw668_f8_signed_route_stage.py','ksw668_f8_weighted_normal_stage.py','warp_native_geometric_receiver.py','check_f8_signed_window.py','check_f8_shrinking_jet.py','check_f8_shrinking_injection.py']
    ident=json.dumps(dict(kind=a.kind,route=a.route,anchor=anchor,source=digest(src),cp=digest(cp),cm=digest(cm),I=digest(I.toarray()),Y=digest(Y.toarray()),dt=h,nt=nt,files={p:hashlib.sha256(Path(__file__).with_name(p).read_bytes()).hexdigest() for p in names}),sort_keys=True)
    if path.exists():
        with np.load(path,allow_pickle=False) as z:
            if z['identity'].item()!=ident:raise ValueError('identity')
            X=z['X'];k=int(z['k']);vals={p:z[p] for p in keys};own={p:z['own_'+p] for p in keys}
            for p,v in dict(X=X,**vals,**{'own_'+p:v for p,v in own.items()}).items():assert digest(v)==z[p+'_sha'].item()
    assert X.shape==(6,1,ny,nr) and 0<=k<=end
    out,A,B=[np.empty_like(X) for _ in range(3)];start=time.monotonic();initial=k;worst=0.
    # Compare actual embedded state against full original solver at resume;
    # other physical modes zero, no artificial change to d=3 operator.
    if k<end:
        Z=np.zeros((6,3,ny,nr));Z[:,:1]=X
        src3=np.zeros((3,nr));src3[:1]=src;cp3=np.zeros_like(src3);cm3=cp3.copy();cp3[:1]=cp;cm3[:1]=cm
        ref=step(Z,T0+k*h,h,coeff,dr,dy,src3,cp3,cm3,a.route)
        step_into(X,out,A,B,T0+k*h,h,coeff,dr,dy,src,cp,cm,a.route)
        assert np.array_equal(ref[:,:1],out) and not np.any(ref[:,1:]);del Z,ref
    def active(obs,n):return any(p[0].start<=n<p[0].stop or np.any(w[:,n]) or nt-1<=n<=end for p,(_,w),b in obs)
    def observe(obs,v,n,x):
        for pos,(p,(idx,w),bank) in enumerate(obs):
            tt,yy,rr,o=p
            if tt.start<=n<tt.stop:v['shrink'][pos]+=np.sum(o[:,0,n-tt.start]*x[0,0,yy,rr],axis=(1,2))
            if np.any(w[:,n]):v['window'][pos]+=np.sum(w[:,n,0]*x[0,0,0,idx],axis=-1)
            if nt-1<=n<=end:v['raw'][pos]+=np.einsum('ciyr,iyr->c',bank[:,n-nt+1,:,0],x[:3,0,:3,:])
    while k<end:
        step_into(X,out,A,B,T0+k*h,h,coeff,dr,dy,src,cp,cm,a.route);X,out=out,X;k+=1
        if a.kind=='shadow':observe(fine_obs,vals,k,X)
        elif active(fine_obs,k) or active(coarse_obs,k):
            # Apply D3.4 map only to physical channels consumed by observations.
            Z=np.zeros((3,1,449,503))
            for c in range(3):Z[c,0,:,:-1]=Y@(I@X[c,0,:,:-1].T).T
            observe(fine_obs,vals,k,Z);observe(coarse_obs,own,k,X)
        if k%128==0 or k==end or time.monotonic()-start>=a.budget:
            assert np.isfinite(X).all() and not np.any(X[..., -1]) and not np.any(X[4,:,1:]) and not np.any(X[5,:,:-1])
            U,P,M,R,J,K=X;D=np.empty_like(U);D[:,0]=(U[:,1]-U[:,0])/dy;D[:,-1]=(U[:,-1]-U[:,-2])/dy;D[:,1:-1]=(U[:,2:]-U[:,:-2])/(2*dy)
            err=float(np.max(abs((P-M)/2-D-R-J-K))/max(1.,*(np.max(abs(x)) for x in (P,M,D,R,J,K))));assert err<1e-10;worst=max(worst,err)
            arrays=dict(X=X,**vals,**{'own_'+p:v for p,v in own.items()});sha={p+'_sha':digest(v) for p,v in arrays.items()}
            tmp=path.with_suffix('.tmp')
            with tmp.open('wb') as f:np.savez(f,identity=ident,k=k,**arrays,**sha);f.flush();os.fsync(f.fileno())
            os.replace(tmp,path)
            with np.load(path,allow_pickle=False) as z:assert int(z['k'])==k and z['identity'].item()==ident and all(digest(z[p])==sha[p+'_sha'] for p in arrays)
            if time.monotonic()-start>=a.budget:break
    return dict(kind=a.kind,route=a.route,initial=initial,cursor=k,end=end,physical_t=float(ts[k]),constraint=worst,sha256=digest(X),source_relative=float(np.sqrt(wf@(sm[0,:-1]-sf[0,:-1])**2/(wf@sf[0,:-1]**2))),source_moments=[float(wc@sc[0,:-1]),float(wf@sm[0,:-1]),float(wf@sf[0,:-1])],observation={p:v.tolist() for p,v in vals.items()},own={p:v.tolist() for p,v in own.items()},seconds=time.monotonic()-start)

if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('work',type=Path);p.add_argument('--kind',choices=['shadow','coarse'],required=True);p.add_argument('--route',choices=['ledger','paired'],required=True);p.add_argument('--budget',type=float,default=15);a=p.parse_args();assert 0<a.budget<=75;print(json.dumps(run(a)),flush=True)
