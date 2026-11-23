"""Original finite radial spectral projections and direct null-ray geometry.
Band components are diagnostics, not individually compact physical sources.
"""
from math import asinh,sqrt,log
import json
from pathlib import Path
import time
import numpy as np
from scipy.linalg import eigh_tridiagonal
from scipy.optimize import brentq
from warp_kernel_refinement_audit import native_setup,source_bank
from warp_resumable_audit import resume_mode,atomic_npz


def ray_geometry(final_t=12.,eps=.04,inside=.012):
    F=lambda t:asinh(t)-sqrt(1+t*t)/t
    span=F(final_t)-F(1);zr=1/final_t
    receiver=sqrt(span**2-(zr-1)**2)-inside
    def emit(s):return brentq(lambda t:F(t)-F(1)-s,1,final_t)
    rows=[]
    for r in (0.,eps/2,eps):
        def interval(s):
            te=emit(s);return (span-s)**2-(zr-1/te)**2-(receiver-r)**2
        s=brentq(interval,0,span*.5);te=emit(s);ze=1/te
        kr=(receiver-r)/(span-s);kz=(zr-ze)/(span-s)
        ve=-1/sqrt(1+te*te);vr=-1/sqrt(1+final_t**2)
        assert abs(kr*kr+kz*kz-1)<1e-11 and ve<kz<vr
        rows.append(dict(radius=r,latest_s=s,kr=kr,kz=kz,emitter_normal=kz-ve,receiver_normal=kz-vr,transport=(zr/ze)**1.5))
    return dict(receiver=receiver,span=span,photon_margin=receiver-eps-log(final_t),rays=rows)


def eigenbasis(s,q):
    r,dr,R=s['r'],s['dr'],s['R'];d=3+4*q
    vol=((r+dr/2)**d-np.maximum(r-dr/2,0)**d)/d
    H=np.sqrt(vol[:-1]);diag=-R[q,:-1,1];off=-R[q,:-2,2]*H[:-1]/H[1:]
    np.testing.assert_allclose(off,-R[q,1:-1,0]*H[1:]/H[:-1],rtol=1e-12,atol=1e-10)
    lam,Q=eigh_tridiagonal(diag,off);assert lam.min()>0
    return H,lam,Q


def project(s,q,src):
    H,lam,Q=eigenbasis(s,q);k=np.sqrt(lam);a=Q.T@(H*src[:-1]);total=a@a
    # Fixed physical-scale bands, plus a separate lattice-frequency diagnostic.
    band=np.digitize(k*s['eps'],[4,8,16]);out=np.zeros((4,1,len(src)))
    for j in range(4):out[j,0,:-1]=(Q@(a*(band==j)))/H
    np.testing.assert_allclose(out.sum(0)[0],src,rtol=1e-9,atol=1e-8*max(1.,np.max(abs(src))))
    return out,dict(high_lattice_fraction=float(np.sum(a[k*s['dr']>1]**2)/total),band_fraction=[float(np.sum(a[band==j]**2)/total) for j in range(4)])


def run(path,seconds=90,mode=None,**params):
    deadline=time.monotonic()+max(0,seconds-5)
    s=native_setup(setup_only=True,**params);bank,_=source_bank(s,True)
    path=Path(path);path.mkdir(parents=True,exist_ok=True)
    t,h=s['t'],s['h'];_,v,b,*_=s['coeff'];w=np.zeros_like(t)
    for n in range(s['nt']+1):w[2*n:2*n+3]+=h*np.array([1/6,2/3,1/6])
    w/=(-v*b**3)
    ks=[];stats=[]
    for q in range(3) if mode is None else [mode]:
        pieces=[];st=[]
        for variant in (0,4):
            p,m=project(s,q,bank[variant,q]);pieces.append(p);st.append(m)
        # A ninth/tenth source is the unprojected original/operator reference.
        rhs=np.concatenate((*pieces,bank[[0,4],q:q+1]),axis=0)
        g=resume_mode(path/f'spec{q}.npz',np.ascontiguousarray(s['obs'][:1,:,:,q:q+1]),h,s['dy'],s['RT'][q:q+1],s['coeff'],rhs,s['active'],deadline)
        if g is None:return False
        g=g[:,0,:];bands=g[:8].reshape(2,4,-1);ref=g[8:]
        err=np.sqrt(np.sum((bands.sum(1)-ref)**2/w,axis=1)/np.sum(ref**2/w,axis=1))
        # Projection may be ill-conditioned in coordinate Euclidean norm, especially d=11.
        assert np.max(err)<1e-5,err
        G=np.einsum('vbt,vct,t->vbc',bands,bands,1/w);C=np.sum(ref**2/w,axis=1)
        print('mode',q,'source',st,'band response C',np.diagonal(G,axis1=1,axis2=2),'total',C,'relative recombination',err,flush=True)
        ks.append(bands);stats.append(st)
    if mode is not None:return True
    bands=np.sum(ks,axis=0);G=np.einsum('vbt,vct,t->vbc',bands,bands,1/w);C=G.sum((1,2))
    atomic_npz(path/'spectral_summary.npz',bands=bands,G=G,C=C,t=t,w=w)
    (path/'source_spectrum.json').write_text(json.dumps(stats,indent=2))
    print('TOTAL',C,'band diagonal',np.diagonal(G,axis1=1,axis2=2),'cancellation',np.trace(G,axis1=1,axis2=2)/C,flush=True)
    return True

if __name__=='__main__':
    import sys
    if len(sys.argv)==1:print(json.dumps(ray_geometry(),indent=2))
    else:run(**json.loads(sys.argv[1]))
