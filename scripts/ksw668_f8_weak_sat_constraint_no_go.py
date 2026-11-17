#!/usr/bin/env python3
"""KSW original a=t TT weak-Israel SAT global-constraint NO-GO.

For physical C=D_y U-(P-M)/2, normal_order=3 has Cdot=0 at each
INTERIOR y node. On the actual weak SAT wall,
 Cdot_wall=((1+v)P_wall-(1-v)M_wall-2G)/dy,
 Cdot_far=(1+v)P_far/dy.
An exact constrained initial field U=y/2, P=1, M=0, G=0 has C=0 at
all nodes yet instantaneous wall/far Cdot=(1+v)/dy.
This is an exact algorithmic boundary counterexample, not a
continuum gravity counterexample or a long-time divergence proof.
"""
import json
import numpy as np
from ksw668_f8_full_coupled_weighted_sbp_energy import setup,coeff
from ksw668_f8_characteristic_constraint_maxcut import actual_stage,D_y,physical_constraint

def witness(t=4/3,dy=.02,ny=11,nr=7):
    if ny<4 or nr<3 or dy<=0:raise ValueError('positive original normal mesh')
    x=setup(t=t,ny=ny,nr=nr,dy=dy,dr=.02,seed=99)
    x['U'][:]=.5*(np.arange(ny)*dy)[None,:,None]
    x['P'][:]=1.
    x['M'][:]=0.
    C0=physical_constraint(x['U'],x['P'],x['M'],dy)
    assert np.max(abs(C0))<1e-12
    Ud,Pd,Md=actual_stage(x,3)
    Cdot=D_y(Ud,dy)-.5*(Pd-Md)
    b,v,_,_,_=coeff(t);expected=(1+v)/dy
    assert np.allclose(Cdot[:,0,:],expected,atol=1e-9)
    assert np.allclose(Cdot[:,-1,:],expected,atol=1e-9)
    assert np.max(abs(Cdot[:,1:-1,:]))<1e-9
    return dict(original_t=t,dy=dy,
       original_initial_physical_constraint_exact_zero=True,
       original_weak_wall_residual=1+v,
       exact_wall_constraint_rate=expected,
       exact_far_constraint_rate=expected,
       exact_interior_constraint_rate=0,
       global_constraint_preservation_closed=False,
       original_Weyl_receiver_accepted=False)
def audit():
    rows=[witness(dy=x) for x in (.04,.02,.01)]
    assert [r['exact_wall_constraint_rate'] for r in rows]==[10.,20.,40.]
    return dict(rows=rows,original_strong_boundary_constraint_weld_OPEN=True,
         physical_graviton_observed=False)
if __name__=='__main__':print(json.dumps(audit(),indent=2))
