"""Resumable signed time-fibre attribution between two completed Gauss runs.
Uses original endpoint receipts, reconstructs only coarse stage history.
Single writer per work directory. No step, mode or receiver is discarded.
"""
import argparse
import hashlib
import json
import os
from pathlib import Path
import tempfile
import time
import numpy as np
from check_f8_gauss_banded import BandedGauss
from check_f8_gauss_checkpoint import identity
from check_f8_gauss_fibre import stages
from check_f8_gauss_action import b,c


def load(path):
    with np.load(path,allow_pickle=False) as z:
        ident=z['identity'].item(); args=json.loads(ident)['grid']; S=BandedGauss(*args)
        if z['phase'].item()!='done' or ident!=identity(S,tuple(args)):
            raise ValueError('requires same-source completed checkpoint')
        return S,z['state'].copy(),ident


def atomic(path,**arrays):
    with tempfile.NamedTemporaryFile(dir=path.parent,delete=False) as f:
        tmp=f.name
        try:
            np.savez(f,**arrays);f.flush();os.fsync(f.fileno());os.replace(tmp,path)
        finally:
            if os.path.exists(tmp):os.unlink(tmp)
    fd=os.open(path.parent,os.O_RDONLY)
    try:os.fsync(fd)
    finally:os.close(fd)


def run(coarse,fine,work,budget=75,every=8):
    C,end,ci=load(coarse);F,target,fi=load(fine)
    assert C.n==F.n and C.fe.n==F.fe.n and C.fe.p==F.fe.p and C.t==F.t and C.r==F.r and np.array_equal(C.src,F.src)
    assert np.array_equal(C.fe.Y,F.fe.Y) and np.array_equal(C.k,F.k) and C.nt<F.nt
    W,_,_=F.weights();Cw,_,_=C.weights();assert all(np.array_equal(W[k],Cw[k]) for k in W)
    assert F.stage[2*F.nt][-1]==0 and C.stage[2*C.nt][-1]==0
    root=Path(__file__).resolve().parent
    hashes={n:hashlib.sha256((root/n).read_bytes()).hexdigest() for n in ('check_f8_gauss_fibre_dual_checkpoint.py','check_f8_gauss_fibre.py')}
    ident=json.dumps(dict(schema=1,coarse=ci,fine=fi,source=hashes,coarse_state=hashlib.sha256(end.tobytes()).hexdigest(),fine_state=hashlib.sha256(target.tobytes()).hexdigest()),sort_keys=True)
    work=Path(work);work.mkdir(parents=True,exist_ok=True);path=work/'cursor.npz'; history=work/'history.npy'
    shape=(C.nt,3,2,C.fe.n,C.n)
    phase,index='history',0;x=np.zeros_like(end);L=np.stack([F.flat(F.terminal(w)) for w in W.values()],axis=-1)
    modal=np.zeros((4,F.n,len(W)));abssum=np.zeros((F.n,len(W)))
    if path.exists():
        with np.load(path,allow_pickle=False) as z:
            if z['identity'].item()!=ident:raise ValueError('history identity mismatch')
            phase,index=z['phase'].item(),int(z['index'].item());x,L,modal,abssum=(z[k].copy() for k in ('x','L','modal','abssum'))
        H=np.lib.format.open_memmap(history,mode='r+')
        if H.shape!=shape or H.dtype!=np.float64:raise ValueError('invalid history array')
        if phase not in ('history','reverse','done') or not 0<=index<=(C.nt if phase=='history' else F.nt) or (phase=='done' and index!=0):raise ValueError('invalid cursor')
        if x.shape!=end.shape or L.shape!=(F.n,F.d,len(W)) or modal.shape!=(4,F.n,len(W)) or abssum.shape!=(F.n,len(W)) or not all(np.isfinite(z).all() for z in (x,L,modal,abssum)):raise ValueError('invalid checkpoint tensors')
    else:H=np.lib.format.open_memmap(history,mode='w+',dtype=np.float64,shape=shape)
    def save():
        if phase=='history':
            H.flush()
            fd=os.open(history,os.O_RDWR)
            try:os.fsync(fd)
            finally:os.close(fd)
        atomic(path,identity=ident,phase=phase,index=index,x=x,L=L,modal=modal,abssum=abssum)
    def sample(j):
        if j==F.nt:return end
        i,r=divmod(j*C.nt,F.nt);theta=r/F.nt
        integ=np.array([(theta*theta/2-c[1]*theta)/(c[0]-c[1]),(theta*theta/2-c[0]*theta)/(c[1]-c[0])])
        return H[i,0]+C.dt*np.einsum('s,sunm->unm',integ,H[i,1:])
    start=time.monotonic();count=0
    while phase!='done':
        if phase=='history' and index==C.nt:
            assert np.array_equal(x,end),'coarse replay does not match endpoint'
            save();phase,index='reverse',F.nt;save()
        elif phase=='reverse' and index==0:phase='done';save()
        elif count and time.monotonic()-start>=budget:break
        else:
            if phase=='history':
                K=stages(C,x,index);H[index,0]=x;H[index,1:]=K;x=x+C.dt*np.einsum('s,sunm->unm',b,K);index+=1
            else:
                j=index-1;r=sample(j+1)-F.advance(sample(j),j)
                z=np.einsum('md,mdr->mr',F.flat(r),L);modal[min(3,4*j//F.nt)]+=z;abssum+=abs(z)
                L,_=F.reverse_flat(L,j);index-=1
            count+=1
            if count%every==0:save()
    save();print('fibre attribution',phase,index,'chunk',count,'seconds',time.monotonic()-start,flush=True)
    if phase=='done':
        expected=np.array([np.sum(w*(C.jets(end)-F.jets(target)),axis=(0,1)) for w in W.values()]).T;got=modal.sum(axis=0)
        err=np.linalg.norm(got-expected)/max(np.linalg.norm(abssum),1e-300);assert err<1e-8,err
        out={name:dict(delta=float(expected[:,k].sum()),attributed=float(got[:,k].sum()),time_quarters=modal[:,:,k].sum(axis=1).tolist(),mode_quarters=[float(got[idx,k].sum()) for idx in np.array_split(np.arange(F.n),4)],time_mode=[[float(modal[t,idx,k].sum()) for idx in np.array_split(np.arange(F.n),4)] for t in range(4)],absolute_residual_contribution=float(abssum[:,k].sum())) for k,name in enumerate(W)}
        print(json.dumps(dict(closure=float(err),coarse_steps=C.nt,fine_steps=F.nt,receivers=out)),flush=True)

if __name__=='__main__':
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('coarse');p.add_argument('fine');p.add_argument('work');p.add_argument('--budget',type=float,default=75);p.add_argument('--every',type=int,default=8);args=p.parse_args();assert args.budget>0 and args.every>0
    run(args.coarse,args.fine,args.work,args.budget,args.every)
