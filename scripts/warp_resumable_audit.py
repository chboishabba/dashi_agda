"""Atomic, time-bounded checkpoint of the native reverse SSPRK3 audit."""
import os, time, json, hashlib, tempfile
from pathlib import Path
import numpy as np
from warp_kernel_refinement_audit import native_setup, source_bank, gram, NAMES
from warp_temporal import stage_into, combine


def atomic_npz(path, **arrays):
    path=Path(path)
    fd,tmp=tempfile.mkstemp(dir=path.parent)
    try:
        with os.fdopen(fd,'wb') as f:
            np.savez(f,**arrays);f.flush();os.fsync(f.fileno())
        os.replace(tmp,path)
    finally:
        if os.path.exists(tmp):os.unlink(tmp)


def fingerprint(*arrays):
    h=hashlib.sha256()
    for a in arrays:
        a=np.ascontiguousarray(a);h.update(str((a.shape,a.dtype)).encode());h.update(a.view(np.uint8))
    return h.hexdigest()


def resume_mode(path,obs,h,dy,RT,coeff,bank,active,deadline,max_steps=None):
    ts,v,b,Z,D,DT=coeff;nt=(len(ts)-3)//2;nb=obs.shape[0]
    path=Path(path);token=fingerprint(obs,np.array([h,dy]),RT,ts,v,b,Z,DT,bank,active)
    if path.exists():
        with np.load(path,allow_pickle=False) as f:
            if str(f['token'])!=token:raise ValueError('checkpoint inputs changed')
            n=int(f['next_n']);x=f['x'];g=f['g']
        if n==-1:return g
    else:
        n=nt;x=np.array(obs[:,2],copy=True,order="C");g=np.zeros((len(bank),nb,len(ts)))
    s1=np.empty_like(x);s2=np.empty_like(x);tmp=np.empty_like(x);zero=np.zeros(nb)
    J=-4*h*bank[:,0]/dy;J[:,-1]=0
    def B(z,out,k):stage_into(z,out,RT,DT[k],v[k],Z[k],dy,h,bank[0],zero,True)
    count=0
    while n>=0 and time.monotonic()<deadline and (max_steps is None or count<max_steps):
        k=2*n;B(x,s2,k+1);combine(s2,s2,s2,2/3,0.)
        B(s2,s1,k+2);combine(s1,s1,s1,.25,0.)
        if active[k+1]:g[:,:,k+1]+=2/3*(J@x[:,2,0,0,:].T)
        if active[k+2]:g[:,:,k+2]+=.25*(J@s2[:,2,0,0,:].T)
        if active[k]:g[:,:,k]+=J@s1[:,2,0,0,:].T
        B(s1,tmp,k);combine(x,x,s2,1/3,.75);combine(x,x,tmp,1.,1.)
        if n>=nt-1:x+=obs[:,n-(nt-1)]
        n-=1;count+=1
    atomic_npz(path,token=token,next_n=n,x=x,g=g)
    print(path,'next_n',n,'steps this slice',count,flush=True)
    return g if n==-1 else None


def run(path,seconds=90,include_operator=True,mode=None,**params):
    # Reserve seconds for checkpoint serialization; never split a RK step.
    deadline=time.monotonic()+max(0,seconds-5)
    s=native_setup(setup_only=True,**params);bank,meta=source_bank(s,include_operator)
    path=Path(path);path.mkdir(parents=True,exist_ok=True)
    t=s['t'];h=s['h'];_,v,b,*_=s['coeff'];qw=np.zeros_like(t)
    for n in range(s['nt']+1):qw[2*n:2*n+3]+=h*np.array([1/6,2/3,1/6])
    w=qw/(-v*b**3);(path/'source.json').write_text(json.dumps(meta,indent=2))
    ks=[]
    for q in range(3) if mode is None else [mode]:
        g=resume_mode(path/f'state{q}.npz',np.ascontiguousarray(s['obs'][:,:,:,q:q+1]),h,s['dy'],s['RT'][q:q+1],s['coeff'],np.ascontiguousarray(bank[:,q:q+1]),s['active'],deadline)
        if g is None:return False
        ks.append(g)
        print('mode',q,'C',np.sum(g*g/w,axis=-1),flush=True)
    if mode is not None:return True
    g=np.array(ks);G,C=gram(g,w)
    atomic_npz(path/'summary.npz',g=g,G=G,C=C,t=t,w=w,quadw=qw,names=NAMES[:len(bank)])
    print('COMPLETE',C,flush=True);return True


if __name__=='__main__':
    import sys
    run(**json.loads(sys.argv[1]))
