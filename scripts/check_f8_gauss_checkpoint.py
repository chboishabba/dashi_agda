"""Resume the original mixed Gauss evolution, with atomic time-step checkpoints.
No change to geometry, source, time step, radial truncation or receiver.
Single writer per checkpoint; use separate paths for separate configurations.
"""
import argparse
import hashlib
import json
import os
from pathlib import Path
import tempfile
import time
import numpy as np
import scipy
from check_f8_gauss_banded import BandedGauss


def identity(S, args):
    root = Path(__file__).resolve().parent
    names = ('check_f8_gauss_checkpoint.py', 'check_f8_gauss_banded.py',
             'check_f8_gauss_action.py', 'check_f8_geometric_adjoint.py',
             'check_f8_geometry_hp.py')
    return json.dumps(dict(schema=1, grid=args, steps=S.nt, dt=S.dt,
        numpy=np.__version__, scipy=scipy.__version__,
        hashes={n:hashlib.sha256((root/n).read_bytes()).hexdigest() for n in names}),sort_keys=True)


def save(path, ident, phase, index, x, lam, gain):
    path.parent.mkdir(parents=True, exist_ok=True)
    with tempfile.NamedTemporaryFile(dir=path.parent, delete=False) as f:
        tmp=f.name
        try:
            np.savez(f, identity=ident, phase=phase, index=index, state=x, adjoint=lam, gain=gain)
            f.flush(); os.fsync(f.fileno())
            os.replace(tmp,path)
        finally:
            if os.path.exists(tmp):os.unlink(tmp)
    fd=os.open(path.parent,os.O_RDONLY)
    try:os.fsync(fd)
    finally:os.close(fd)


def advance_chunk(S, path, ident, budget=75, max_steps=None, every=8):
    start=time.monotonic(); path=Path(path)
    W,F,R=S.weights(); names=list(W)
    x=np.zeros((2,S.fe.n,S.n));lam=np.zeros((S.n,S.d,len(W)));gain=np.zeros((S.n,len(W)))
    phase,index='forward',0
    if path.exists():
        with np.load(path,allow_pickle=False) as z:
            if z['identity'].item()!=ident:raise ValueError('checkpoint identity mismatch')
            phase,index=z['phase'].item(),int(z['index'].item())
            for key,arr in [('state',x),('adjoint',lam),('gain',gain)]:
                if z[key].shape!=arr.shape or z[key].dtype!=arr.dtype or not np.isfinite(z[key]).all():raise ValueError('invalid '+key)
            x,lam,gain=(z[k].copy() for k in ('state','adjoint','gain'))
        if phase not in ('forward','reverse','done') or not 0<=index<=S.nt or (phase=='done' and index!=0):raise ValueError('invalid checkpoint cursor')
    count=0
    while phase!='done':
        if phase=='forward' and index==S.nt:
            lam=np.stack([S.flat(S.terminal(w)) for w in W.values()],axis=-1)
            phase,index='reverse',S.nt
            save(path,ident,phase,index,x,lam,gain)
        elif phase=='reverse' and index==0:
            phase='done';save(path,ident,phase,index,x,lam,gain)
        elif count and (time.monotonic()-start>=budget or (max_steps is not None and count>=max_steps)):
            break
        else:
            if phase=='forward':x=S.advance(x,index);index+=1
            else:
                lam,g=S.reverse_flat(lam,index-1);gain+=g;index-=1
            count+=1
            if count%every==0:save(path,ident,phase,index,x,lam,gain)
    save(path,ident,phase,index,x,lam,gain)
    print('checkpoint',phase,index,'of',S.nt,'chunk steps',count,'seconds',time.monotonic()-start,flush=True)
    if phase=='done':
        jets=S.jets(x);out={}
        for j,(name,w) in enumerate(W.items()):
            f=np.sum(w*jets,axis=(0,1));err=np.linalg.norm(f-gain[:,j])/max(np.linalg.norm(f),1e-300)
            assert err<1e-8,(name,err)
            out[name]=dict(forward=float(f.sum()),adjoint=float(gain[:,j].sum()),relative=float(err))
        flux=float(np.sum(F*jets));bulk=float(np.sum(R*jets));delta=out['E5_direct']['forward']-out['E5_SMS']['forward']
        residual=delta+(1/S.t+1/(2*S.t**3))*flux+bulk/(3*S.t**2)
        print(json.dumps(dict(receivers=out,wall_flux=flux,bulk_residual=bulk,off_shell_identity_residual=residual)),flush=True)
        assert abs(residual)<1e-10*max(1,abs(delta),abs(flux),abs(bulk))
    return phase,x,lam,gain


def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('checkpoint',type=Path);p.add_argument('--grid',nargs=4,default=['360','20','3','.005'])
    p.add_argument('--budget',type=float,default=75);p.add_argument('--max-steps',type=int);p.add_argument('--every',type=int,default=8)
    opts=p.parse_args();assert opts.budget>0 and opts.every>0 and (opts.max_steps is None or opts.max_steps>0)
    args=tuple(map(int,opts.grid[:3]))+(float(opts.grid[3]),)
    S=BandedGauss(*args);advance_chunk(S,opts.checkpoint,identity(S,args),opts.budget,opts.max_steps,opts.every)

if __name__=='__main__':main()
