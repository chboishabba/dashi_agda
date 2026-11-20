"""Geometry-first terminal weak/pointwise diagnostic on a completed checkpoint.
Weak residual uses reconstructed terminal jets, not an independent evolution.
Modal prefix sums are diagnostics, not a substitute receiver or cutoff proof.
"""
import argparse
import json
import numpy as np
from check_f8_gauss_banded import BandedGauss
from check_f8_gauss_checkpoint import identity


def diagnose(path):
    with np.load(path, allow_pickle=False) as z:
        ident=z['identity'].item(); args=json.loads(ident)['grid']
        S=BandedGauss(*args)
        if ident!=identity(S,tuple(args)) or z['phase'].item()!='done':
            raise ValueError('requires matching completed checkpoint')
        x=z['state'].copy()
    jets=S.jets(x); W,F,R=S.weights()
    M,C,K,b,v,a,g=S.stage[2*S.nt]
    Md,Cd,_=S.fe.matrices(b,v,True)
    u,m=x; q,qtt=jets[1:]; mv=S.fe.mv
    mt=mv(M,qtt)+mv(Md,q)-a*mv(C,u)-v*mv(Cd,u)-v*mv(C,q)
    terms=[mt,v*mv(C,q,True),(1-v*v)*mv(K,u),mv(M,u)*S.k2]
    d=np.zeros_like(q); d[-1]=(b+S.fe.Y[-1])**-3*q[-1]
    f=np.zeros_like(q); f[0]=g*S.src
    residual=sum(terms)+d-f
    weak=np.linalg.norm(residual)/max(sum(np.linalg.norm(t) for t in terms+[d,f]),1e-300)
    constraint=mv(M,q)-m-v*mv(C,u)
    constraint_rel=np.linalg.norm(constraint)/max(np.linalg.norm(mv(M,q))+np.linalg.norm(m)+np.linalg.norm(v*mv(C,u)),1e-300)
    prefixes=sorted(set([S.n//4,S.n//2,3*S.n//4,S.n]))
    out={}
    for name,w in W.items():
        y=np.sum(w*jets,axis=(0,1))
        out[name]=dict(total=float(y.sum()),absolute_sum=float(abs(y).sum()),prefix={i:float(y[:i].sum()) for i in prefixes})
    flux=float(np.sum(F*jets)); bulk=float(np.sum(R*jets))
    wall_term=-(1/S.t+1/(2*S.t**3))*flux; bulk_term=-bulk/(3*S.t**2)
    print(json.dumps(dict(grid=args,steps=S.nt,dt=S.dt,weak=weak,constraint=constraint_rel,receivers=out,wall_flux=flux,bulk_residual=bulk,wall_term=wall_term,bulk_term=bulk_term),sort_keys=True),flush=True)
    assert weak<1e-10 and constraint_rel<1e-10

if __name__=='__main__':
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('checkpoints',nargs='+');args=p.parse_args()
    for path in args.checkpoints:diagnose(path)
