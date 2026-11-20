"""Atomic completed-step checkpoint for the original native SSPRK3 driver."""
import hashlib,json,os,tempfile,time
from pathlib import Path
import numpy as np
import numba
import sympy

class NativeCheckpoint:
    def __init__(self,path,config,dims,src,cp,cm):
        self.path=Path(path);self.dims=dims;self.nt=config['nt']
        root=Path(__file__).resolve().parent
        files=('ksw668_f8_ssprk_checkpoint.py','ksw668_f8_tt_multipole.py','ksw668_f8_fv_source_flux.py')
        self.identity=json.dumps(dict(schema=1,config=config,dims=dims,
            versions=[np.__version__,numba.__version__,sympy.__version__],
            source={n:hashlib.sha256((root/n).read_bytes()).hexdigest() for n in files},
            arrays=[hashlib.sha256(x.tobytes()).hexdigest() for x in (src,cp,cm)]),sort_keys=True)
    def start(self):self.t=time.monotonic()
    def expired(self,budget):return time.monotonic()-self.t>=budget
    def save(self,cursor,U,P,M,*walls):
        self.path.parent.mkdir(parents=True,exist_ok=True)
        with tempfile.NamedTemporaryFile(dir=self.path.parent,delete=False) as f:
            tmp=f.name
            try:
                np.savez(f,identity=self.identity,cursor=cursor,U=U,P=P,M=M,
                    **{f'w{i}':np.empty(0) if w is None else w for i,w in enumerate(walls)})
                f.flush();os.fsync(f.fileno());os.replace(tmp,self.path)
            finally:
                if os.path.exists(tmp):os.unlink(tmp)
        fd=os.open(self.path.parent,os.O_RDONLY)
        try:os.fsync(fd)
        finally:os.close(fd)
    def load(self):
        if not self.path.exists():return None
        with np.load(self.path,allow_pickle=False) as z:
            if z['identity'].item()!=self.identity:raise ValueError('checkpoint identity mismatch')
            cursor=int(z['cursor'].item())
            if not 0<=cursor<=self.nt+1:raise ValueError('invalid cursor')
            arrays=[z[k].copy() for k in ('U','P','M')]
            walls=[z[f'w{i}'].copy() for i in range(4)]
            for x in arrays:
                if x.shape!=self.dims or x.dtype!=np.float64 or not np.isfinite(x).all():raise ValueError('invalid field')
            for i,w in enumerate(walls):
                required=cursor>=self.nt+(i%2)
                if required:
                    if w.shape!=(self.dims[0],self.dims[2]) or w.dtype!=np.float64 or not np.isfinite(w).all():raise ValueError('invalid terminal history')
                elif w.shape!=(0,):raise ValueError('unexpected terminal history')
            return (cursor,*arrays,*(None if w.size==0 else w for w in walls))
