"""Fresh-process checkpoint restart on LIV small-box harness, not propagate()."""
import sys, subprocess, tempfile
from pathlib import Path
import numpy as np
from check_f8_liv_checkpoint_parity import rhs, step, T0, dt, nt, ny,nr,dr,dy,src,cp,cm,NativeCheckpoint

def run(aff,path,stop,output):
    config=dict(nt=nt,affine_stage=aff,dr=dr,dy=dy,dt=dt)
    ck=NativeCheckpoint(path,config,(3,ny,nr),src,cp,cm)
    saved=ck.load()
    if saved is None: cursor=0; X=np.zeros((3,3,ny,nr)); walls=[None]*4
    else:
        cursor,*fields=saved; X=np.stack(fields[:3]);walls=fields[3:]
    for it in range(cursor,nt+1):
        T=T0+it*dt
        if it in (nt-1,nt):
            j=it-(nt-1);walls[j]=X[0,:,0,:].copy();walls[j+2]=rhs(X,T,aff)[0,:,0,:].copy()
        X=step(X,T,aff)
        if it+1==stop:
            ck.save(it+1,*X,*walls)
            return
    walls.extend([X[0,:,0,:].copy(),rhs(X,T0+(nt+1)*dt,aff)[0,:,0,:].copy()])
    np.savez(output,*X,*walls)

def main():
    with tempfile.TemporaryDirectory() as tmp:
        tmp=Path(tmp); count=0
        def launch(aff,path,stop,out):
            subprocess.run([sys.executable,__file__,str(int(aff)),str(path),str(stop),str(out)],check=True)
        for aff in (False,True):
            ref=tmp/'reference.npz'; launch(aff,tmp/'unused.npz',-1,ref)
            for cuts in ((65,130),(159,160,161)):
                path=tmp/'resume.npz'; out=tmp/'result.npz';path.unlink(missing_ok=True)
                for cut in cuts:launch(aff,path,cut,out)
                launch(aff,path,-1,out)
                with np.load(ref) as a,np.load(out) as b:
                    for k in a.files:np.testing.assert_array_equal(a[k],b[k]);count+=1
            print('route',aff,'fresh process parity PASS',flush=True)
        print(count,'array comparisons PASS')
if __name__=='__main__':
    if len(sys.argv)>1:run(bool(int(sys.argv[1])),Path(sys.argv[2]),int(sys.argv[3]),Path(sys.argv[4]))
    else:main()
