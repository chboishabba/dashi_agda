"""Resume derivative-free pilot from a recorded conservative H0-converted bound.
The printed converted bound >= the actual H_theta accumulator; using it as
H_theta input only loosens the bound. This is not a bitwise trajectory restart.
"""
import sys,json,time,hashlib
from fractions import Fraction as Q
from pathlib import Path
import numpy as np
import check_f8_vector_interval as vi
from check_f8_boundary_energy import rate,advance
from check_f8_local_dual_weld import I
from run_f8_bidirectional_low_dual import box_at,KD,K,H,END,DY,NY,BS,digest

def run(root):
    start=time.monotonic();log=(root/'boundary.log').read_bytes();prefix=[]
    for line in log.decode().splitlines():
        if line.startswith('boundary replay '):
            _,_,i,val=line.split(' ',3);prefix.append((int(i),json.loads(val)))
    cursor,initial=prefix[-1];assert 0<cursor<=END and cursor%BS==0
    states=np.load(root/'dual_jets.npy',mmap_mode='r');old=np.load(root/'dual_bounds.npy');meta=json.loads((root/'reverse.json').read_text());assert digest(states)==meta['jets_sha'] and digest(old)==meta['bounds_sha']
    theta=[Q(1,32),Q(1,8)];B=np.array(initial);maxgamma=[Q(0),Q(0)];k=I(K[0].l,K[-1].h)
    def batch(x):return np.transpose(x,(1,2,0,3)).reshape(4,NY,-1)
    def tile(x,m):return vi.V(np.tile(x.l,m),np.tile(x.h,m))
    for i in reversed(range(0,cursor,BS)):
        j=i+BS;box,rev,g,gt,q,qf,qft,_,_=box_at(i)
        R,G,*_=vi.primal(batch(states[i+1:j+1]),batch(states[i:j]),H,DY,tile(KD,BS),rev,tile(qf,BS),-tile(qft,BS));R=R.reshape(BS,4);G=G.reshape(BS,4)
        for a,t in enumerate(theta):
            gamma=rate(box,k,t,True);maxgamma[a]=max(maxgamma[a],gamma)
            for z in range(BS-1,-1,-1):B[a]=advance(B[a],H,KD,rev,R[z],G[z],t,gamma)
    final=[(vi.V(B[a])/(1-vi.rat(t)).sqrt()).h.tolist() for a,t in enumerate(theta)]
    result=dict(seconds=time.monotonic()-start,resume_cursor=cursor,logged_incoming_H0=initial,prefix_log_sha256=hashlib.sha256(log).hexdigest(),theta=[str(t) for t in theta],prefix_remaining_maxgamma=list(map(float,maxgamma)),final_H0_bounds=final,old_final=old[0].tolist(),scope='whole reverse endpoint upper bound from logged prefix and conservative restart; no full replacement time ledger or forward re-pairing')
    (root/'boundary_resume.json').write_text(json.dumps(result));return result
if __name__=='__main__':print(json.dumps(run(Path(sys.argv[1]))),flush=True)
