"""Independent old-stage and sparse-transpose parity on the cached Euler map."""
import numpy as np
from numba import set_num_threads
from ksw668_f8_tt_multipole import stage
from warp_stage_adjoint import transpose
from warp_temporal import coefficients,radial_bands,stage_into

set_num_threads(4)
rng=np.random.default_rng(1531)
for order in (3,4):
    for ny,nr in ((7,11),(68,252),(251,539)):
        dr,dy,h=.008,.012,.0015
        R,RT=radial_bands(nr,dr)
        cp=np.zeros((3,nr));cm=cp.copy()
        for q in range(3):
            d=3+4*q;j=np.arange(1,nr);den=(j+.5)**d-(j-.5)**d
            cp[q,1:]=d*(j+.5)**(d-1)/den;cm[q,1:]=d*(j-.5)**(d-1)/den
        ts,v,b,Z,D,DT=coefficients(np.array([0.,1.,2.6]),ny,dy,order)
        x=rng.normal(size=(1,3,3,ny,nr));x[..., -1]=0
        source=rng.normal(size=(3,nr));source[:,-1]=0
        amp=np.array([.73]);out=np.empty_like(x);ref=np.empty_like(x[0])
        for j in range(len(ts)):
            stage(*x[0],*ref,dr,dy,b[j],v[j],amp[0],source,cp,cm,order)
            ref=x[0]+h*ref
            stage_into(x,out,R,D[j],v[j],Z[j],dy,h,source,amp,False)
            np.testing.assert_allclose(out[0],ref,rtol=1e-11,atol=1e-10)
            ferr=np.max(abs(out[0]-ref))
            ref=x[0]+h*transpose(x[0],dr,dy,b[j],v[j],order)
            stage_into(x,out,RT,DT[j],v[j],Z[j],dy,h,source,amp,True)
            np.testing.assert_allclose(out[0],ref,rtol=1e-11,atol=1e-10)
            print(order,ny,nr,j,'forward',ferr,'adjoint',np.max(abs(out[0]-ref)),flush=True)
