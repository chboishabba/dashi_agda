"""Derivative-free dual error replay from completed reverse Hermite jet history.
No new PDE evolution. Compare two fixed positive symmetrizers independently.
"""
import sys,json,time
from fractions import Fraction as Q
from pathlib import Path
import numpy as np
import check_f8_vector_interval as vi
from check_f8_boundary_energy import rate,advance
from check_f8_local_dual_weld import I
from run_f8_bidirectional_low_dual import box_at,KD,K,H,END,DY,NY,BS,trace,digest

def run(root):
    start=time.monotonic();states=np.load(root/'dual_jets.npy',mmap_mode='r');old=np.load(root/'dual_bounds.npy');meta=json.loads((root/'reverse.json').read_text());assert digest(states)==meta['jets_sha'] and digest(old)==meta['bounds_sha']
    theta=[Q(1,32),Q(1,8)];B=np.zeros((2,4));bounds=np.zeros((2,END,4));maxgamma=[Q(0),Q(0)];k=I(K[0].l,K[-1].h)
    def batch(x):return np.transpose(x,(1,2,0,3)).reshape(4,NY,-1)
    def tile(x,m):return vi.V(np.tile(x.l,m),np.tile(x.h,m))
    for i in reversed(range(0,END,BS)):
        j=min(i+BS,END);m=j-i;box,rev,g,gt,q,qf,qft,_,_=box_at(i)
        A=batch(states[i+1:j+1]);D=batch(states[i:j]);R,G,GT,*_=vi.primal(A,D,H,DY,tile(KD,m),rev,tile(qf,m),-tile(qft,m));R=R.reshape(m,4);G=G.reshape(m,4)
        for a,t in enumerate(theta):
            gamma=rate(box,k,t,True);maxgamma[a]=max(maxgamma[a],gamma)
            for z in range(m-1,-1,-1):
                B[a]=advance(B[a],H,KD,rev,R[z],G[z],t,gamma)
                bounds[a,i+z]=(vi.V(B[a])/(1-vi.rat(t)).sqrt()).h
        if i%1024==0:print('boundary replay',i,bounds[:,i].tolist(),flush=True)
    result=dict(seconds=time.monotonic()-start,theta=[str(t) for t in theta],maxgamma=list(map(float,maxgamma)),final_H0_bounds=bounds[:,0].tolist(),old_final=old[0].tolist(),bounds_sha=digest(bounds),scope='whole reverse scalar clock, conditional outward arithmetic and exact energy theorem; no forward re-pairing')
    np.save(root/'dual_boundary_bounds.npy',bounds);(root/'boundary.json').write_text(json.dumps(result));return result
if __name__=='__main__':print(json.dumps(run(Path(sys.argv[1]))),flush=True)
