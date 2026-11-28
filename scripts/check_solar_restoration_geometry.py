"""Bidi finite-return tests on original exponential thermal law."""
import numpy as np
import sympy as S
from solar_restoration_geometry import thermal_return_geometry,analytic_support_return_obstruction

def run():
    a,b,p=S.symbols('a b p',positive=True)
    assert all((b*p*a**i).is_positive for i in range(6))
    n,k,h=S.symbols('n k h',positive=True)
    assert (n*S.exp(-k*h)).is_positive
    heat=np.array([[2.,0.],[0.,3.]]);cap=np.array([1.,2.]);cool=np.array([.3,.7]);dt=.25
    tol=1e-8;out=thermal_return_geometry(heat,dt,cap,cool,3,0,tol)
    decay=np.exp(-dt*cool/cap); beta=-np.expm1(-dt*cool/cap)/cool
    theta=np.zeros(2)
    for p in np.tile(heat,(3,1)):theta=decay*theta+beta*p
    assert np.isclose(np.log(np.linalg.norm(theta)),out['log_terminal_norm'])
    necessary=out['necessary_tail_steps_candidate'];sufficient=out['sufficient_tail_steps_candidate']
    assert necessary<=sufficient and np.linalg.norm(theta*decay**sufficient)<=tol
    if necessary>0: assert np.linalg.norm(theta*decay**(necessary-1))>tol
    under=thermal_return_geometry(heat,dt,cap,cool,3,100000,0.)
    assert under['exact_zero_return_obstructed'] and not under['finite_exact_tail_exists'] and not under['tolerance_return_candidate']
    assert under['log_terminal_norm'] < -700
    assert thermal_return_geometry(heat*0,dt,cap,cool,3,0,0.)['finite_exact_tail_exists']
    assert analytic_support_return_obstruction([True,False],[True,True])['obstructed_indices']==[[1]]
    assert not analytic_support_return_obstruction([True,False],[True,False])['exact_zero_population_return_obstructed']
    print(dict(status='RESTORATION_GEOMETRY_PASS',necessary_tail=necessary,sufficient_tail=sufficient,underflow_log_norm=under['log_terminal_norm']))
if __name__=='__main__':run()
