"""Matched-domain old characteristic vs geometry-first variational comparison."""
import inspect
import numpy as np
from math import asinh,sqrt
import check_f8_common_prepotential as prior
import check_f8_geometry_variational as geom
from check_f8_bianchi_residual import bianchi

def run():
    # Preserve the exact earlier stage and source, changing only its domain.
    scope=dict(vars(prior));exec(inspect.getsource(prior.evolve).replace('R=3.2;','R=4.3;'),scope)
    xyz,P=prior.angular();F=lambda t:asinh(t)-sqrt(1+t*t)/t
    X=np.r_[F(11.8),2.52*np.array([2.,3.,6.])/7,1/11.8+.06]
    for Ny in (71,141):
        H,m=scope['evolve'](180,Ny,.00125,True)
        v=prior.make_evaluator(H,m,True,xyz,P);a,Q=prior.diagnostics(v,X)
        print('old matched',Ny,'h Q E div',a,'E/h',a[2]/a[0],'Bianchi',bianchi(v,X,2e-4,2e-5),flush=True)
if __name__=='__main__':run()
