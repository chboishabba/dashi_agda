import math,time,json,sys,hashlib
from pathlib import Path
import numpy as np
from scipy.optimize import brentq
from ksw668_f8_tt_multipole import F
from ksw668_f8_fv_source_flux import exact_cell_averages
from ksw668_f8_signed_route_stage import step
route,dr,dy,ny=sys.argv[1:];dr=float(dr);dy=float(dy);ny=int(ny)
T0=F(1);span=F(12)-T0;nt=math.ceil(span/.0006);h=span/nt;end=math.ceil(.065/h)+1
nr=math.ceil(3.01/dr)+1;src=exact_cell_averages(.04,np.arange(nr)*dr,dr);cp=np.zeros_like(src);cm=cp.copy()
for q,d in enumerate((3,7,11)):
    for j in range(1,nr):
        den=(j+.5)**d-(j-.5)**d;cp[q,j]=d*(j+.5)**(d-1)/den;cm[q,j]=d*(j-.5)**(d-1)/den

def coeff(T):
    t=brentq(lambda t:F(t)-T,.5,25);v=-1/math.sqrt(1+t*t);q=2*(T-T0)/.065-1
    return v,1/t,-6*math.sqrt(1-v*v)*t*math.exp(1-1/(1-q*q)) if abs(q)<1 else 0.
start=time.monotonic();k=0;path=Path(f'{route}-{nr}-{ny}-prefix.npz');X=np.zeros((6,3,ny,nr))
if path.exists():
    with np.load(path,allow_pickle=False) as z:X=z['X'];k=int(z['k'])
initial=k
while k<end:
    X=step(X,T0+k*h,h,coeff,dr,dy,src,cp,cm,route);k+=1
    if k%8==0 or k==end:
        assert np.isfinite(X).all() and not np.any(X[..., -1]);assert not np.any(X[4,:,1:]) and not np.any(X[5,:,:-1])
        with path.with_suffix('.tmp').open('wb') as f:np.savez(f,X=X,k=k)
        path.with_suffix('.tmp').replace(path)
        with np.load(path,allow_pickle=False) as z:
            assert z['k']==k and np.array_equal(X,z['X']);X=z['X']
        if time.monotonic()-start>12:break
U,P,M,R,J,K=X;D=np.empty_like(U);D[:,0]=(U[:,1]-U[:,0])/dy;D[:,-1]=(U[:,-1]-U[:,-2])/dy;D[:,1:-1]=(U[:,2:]-U[:,:-2])/(2*dy)
q=(P-M)/2-D-R-J-K;scale=max(1.,np.max(abs(P)),np.max(abs(M)),np.max(abs(D)),np.max(abs(R)),np.max(abs(J)),np.max(abs(K)))
print(json.dumps(dict(route=route,nr=nr,ny=ny,dr=dr,dy=dy,nt=nt,h=h,initial=initial,steps=k,requested=end,elapsed_T=k*h,source_complete=k==end,source_nonzero=np.count_nonzero(src,axis=1).tolist(),constraint_scaled=float(np.max(abs(q))/scale),max_state=float(np.max(abs(X))),sha256=hashlib.sha256(X.tobytes()).hexdigest(),seconds=time.monotonic()-start)),flush=True)
