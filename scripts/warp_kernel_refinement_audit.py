"""Opt-in audit of native weighted adjoint: source moments and kernel norms.
No default-source change; operator variant requires its own support guard.
"""
import json
from pathlib import Path
from math import log
import numpy as np
from scipy.integrate import quad
from ksw668_f8_fv_source_flux import compact_bump
from warp_temporal import stage_into, combine, propagate
from warp_temporal_weighted_adjoint import run as native_setup

NAMES = ('original', 'vanishing', 'leading', 'next', 'operator')


def targets():
    I = lambda k: quad(lambda u: u**k*compact_bump(u), 0, 1, epsabs=1e-13)[0]
    return ([0., 0., 48*I(2), 336*I(4)],
            [0., 120*I(2), 720*I(4)], [27*I(2), 99*I(4)])


def source_bank(s, include_operator=False):
    r, dr, eps, src, R = (s[k] for k in ('r','dr','eps','src','R'))
    x = r/eps
    support = (r-dr/2 < eps)
    bank = np.repeat(src[None], 5, axis=0)
    metadata = []
    for q, target in enumerate(targets()):
        d = 3+4*q
        vol = ((r+dr/2)**d-np.maximum(r-dr/2,0)**d)/d/eps**d
        A = x[support][None,:]**(2*np.arange(len(target))[:,None])
        v = vol[support]; m = v*src[q,support]
        for k,n in enumerate((2 if q==0 else 1, len(target)-1, len(target)),1):
            H = A[:n]
            residual = np.asarray(target[:n])-H@m
            correction = H.T@np.linalg.solve((H*v)@H.T,residual)
            bank[k,q,support] += correction
            np.testing.assert_allclose(H@(v*bank[k,q,support]),target[:n],rtol=1e-9,atol=1e-9)
        if q<2:
            bavg = np.zeros_like(r)
            for j in np.flatnonzero(support):
                lo=max(0,r[j]-dr/2)/eps; hi=min(eps,r[j]+dr/2)/eps
                mass=quad(lambda u:u*u*compact_bump(u),lo,hi,epsabs=1e-13)[0]
                if q==1:
                    def end(u):
                        return 0. if u==0 or u>=1 else (-2*u**5/(1-u*u)**2-5*u**3)*compact_bump(u)
                    mass=end(hi)-end(lo)+15*mass
                bavg[j]=mass/vol[j]
            def L(y):
                a=R[q,:,1]*y
                a[1:]+=R[q,1:,0]*y[:-1];a[:-1]+=R[q,:-1,2]*y[1:]
                a[-1]=0
                return eps**2*a
            bank[4,q]=(2/5)*L(L(bavg)) if q==0 else (4/7)*L(bavg)
        moments = (bank[:,q]*vol)@((x[None,:]**(2*np.arange(len(target))[:,None])).T)
        n=2 if q<2 else 1
        np.testing.assert_allclose(moments[4,:n],target[:n],rtol=1e-9,atol=1e-9)
        margins=[s['rx']-log(s['final_t'])-max(r[y!=0])-dr/2 for y in bank[:,q]]
        l2=np.sqrt(np.sum(vol*(bank[:,q]-src[q])**2,axis=1)/np.sum(vol*src[q]**2))
        metadata.append(dict(ell=2*q,target=list(target),moments=moments.tolist(),margins=margins,relative_source_l2=l2.tolist()))
    if include_operator:
        assert all(m['margins'][4]>0 for m in metadata), 'operator stencil support violates discrete photon guard'
    return bank if include_operator else bank[:4], metadata


def adjoint_bank(obs,h,dy,RT,coeff,bank,active):
    """Same native transpose and stages; contract several RHS against one adjoint."""
    ts,v,b,Z,D,DT=coeff; nt=(len(ts)-3)//2
    nb=obs.shape[0]; assert obs.shape[3]==1 and bank.shape[1]==1
    x=np.ascontiguousarray(obs[:,2]);s1=np.empty_like(x);s2=np.empty_like(x);tmp=np.empty_like(x)
    zero=np.zeros(nb);g=np.zeros((len(bank),nb,len(ts)));J=-4*h*bank[:,0]/dy;J[:,-1]=0
    def B(z,out,k):
        stage_into(z,out,RT,DT[k],v[k],Z[k],dy,h,bank[0],zero,True)
    for n in range(nt,-1,-1):
        k=2*n;B(x,s2,k+1);combine(s2,s2,s2,2/3,0.)
        B(s2,s1,k+2);combine(s1,s1,s1,.25,0.)
        if active[k+1]:g[:,:,k+1]+=2/3*(J@x[:,2,0,0,:].T)
        if active[k+2]:g[:,:,k+2]+=.25*(J@s2[:,2,0,0,:].T)
        if active[k]:g[:,:,k]+=J@s1[:,2,0,0,:].T
        B(s1,tmp,k);combine(x,x,s2,1/3,.75);combine(x,x,tmp,1.,1.)
        if n>=nt-1:x+=obs[:,n-(nt-1)]
    return g


def gram(g,w):
    """g has shape (mode,variant,channel,time), w positive."""
    G=np.einsum('qvct,pvct,t->vcqp',g,g,1/w)
    total=np.sum(g,axis=0); C=np.sum(total**2/w,axis=-1)
    np.testing.assert_allclose(G.sum(axis=(-2,-1)),C,rtol=1e-9,atol=1e-24)
    return G,C


def density(g,w,q):
    """Isometric piecewise constant embedding on quadrature-mass time cells."""
    return np.r_[0.,np.cumsum(q)], g/np.sqrt(w*q)


def kernel_distance(a,b):
    """Return relative L2 distance (denominator b) and cosine; zero-extend."""
    e,x=density(a['g'].sum(0),a['w'],a['quadw'])
    f,y=density(b['g'].sum(0),b['w'],b['quadw'])
    u=np.unique(np.r_[e,f]);m=(u[:-1]+u[1:])/2;du=np.diff(u)
    def sample(edges,z):
        i=np.searchsorted(edges,m,side='right')-1
        out=np.zeros(z.shape[:-1]+(len(m),));ok=(i>=0)&(i<z.shape[-1]);out[...,ok]=z[...,i[ok]]
        return out
    x,y=sample(e,x),sample(f,y)
    xx=np.sum(x*x*du,axis=-1);yy=np.sum(y*y*du,axis=-1);xy=np.sum(x*y*du,axis=-1)
    np.testing.assert_allclose(xx,a['C'],rtol=1e-10,atol=1e-24)
    np.testing.assert_allclose(yy,b['C'],rtol=1e-10,atol=1e-24)
    return np.sqrt(np.sum((x-y)**2*du,axis=-1)/yy),xy/np.sqrt(xx*yy)


def audit(path, mode=None, include_operator=False, **params):
    s=native_setup(setup_only=True,**params);bank,meta=source_bank(s,include_operator)
    path=Path(path);path.mkdir(parents=True,exist_ok=True)
    conf={k:s[k] for k in ('dr','dy','dt','eps','final_t','pulse','r_outer','y_outer','order','nt')}
    conf.update(version=1,include_operator=include_operator)
    manifest=path/'manifest.json'
    if manifest.exists():assert json.loads(manifest.read_text())==conf
    else:
        assert not list(path.glob('*.npz'))
        manifest.write_text(json.dumps(conf,sort_keys=True))
    (path/'source.json').write_text(json.dumps(meta,indent=2))
    h=s['h'];nt=s['nt'];t=s['t'];_,v,b,*_=s['coeff']
    qweight=np.zeros_like(t)
    for n in range(nt+1):qweight[2*n:2*n+3]+=h*np.array([1/6,2/3,1/6])
    w=qweight/(-v*b**3)
    for q in (range(3) if mode is None else [mode]):
        assert 0<=q<3
        obs=np.ascontiguousarray(s['obs'][:,:,:,q:q+1]);rt=s['RT'][q:q+1]
        g=adjoint_bank(obs,h,s['dy'],rt,s['coeff'],np.ascontiguousarray(bank[:,q:q+1]),s['active'])
        assert np.isfinite(g).all()
        np.savez(path/f'kernel{q}.npz',g=g,t=t,w=w,quadw=qweight)
        print('audit mode',q,'individual compliance',np.sum(g*g/w,axis=-1),flush=True)
    if not all((path/f'kernel{q}.npz').exists() for q in range(3)):return
    files=[np.load(path/f'kernel{q}.npz') for q in range(3)]
    for a in files:
        np.testing.assert_array_equal(a['t'],t);np.testing.assert_array_equal(a['w'],w)
    g=np.array([a['g'] for a in files]);G,C=gram(g,w)
    np.savez(path/'summary.npz',g=g,G=G,C=C,t=t,w=w,quadw=qweight,names=NAMES[:len(bank)])
    print('compliance',C,'cancellation',np.trace(G,axis1=-2,axis2=-1)/C,flush=True)

if __name__=='__main__':
    import sys
    if sys.argv[1]=='compare':
        a,b=map(np.load,sys.argv[2:4]);print('relative norm, cosine',kernel_distance(a,b))
    else:audit(**json.loads(sys.argv[1]))
