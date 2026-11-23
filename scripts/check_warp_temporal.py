import numpy as np
from warp_temporal import *
from numba import set_num_threads
set_num_threads(4)
rng=np.random.default_rng(1530)
for order in (3,4):
    ny,nr=7,11; h,dy,dr=.001,.012,.008
    t=np.arange(23)*h/2; C=coefficients(t,ny,dy,order);R,RT=radial_bands(nr,dr)
    src=rng.normal(size=(3,nr));src[:,-1]=0
    obs=rng.normal(size=(4,3,3,3,ny,nr));obs[..., -1]=0
    f=rng.normal(size=(5,len(t)))
    g=propagate(f,obs,h,dy,R,RT,C,src,True)
    y=propagate(f,obs,h,dy,R,RT,C,src)
    np.testing.assert_allclose(y,f@g.T,rtol=1e-10,atol=1e-10)
    print(order,'batch forward-adjoint 20/20',np.max(abs(y-f@g.T)),flush=True)
