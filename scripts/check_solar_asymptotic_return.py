"""Original birth-free reaction tail and exact frozen indexed field return."""
import numpy as np
import sympy as S
from solar_physical_causal import reaction
from solar_physical_cone import timed_step
from solar_asymptotic_return import recombination_tail_geometry,source_off_tail_receipt
from solar_frozen_tail_certificate import tail_stage_matrix,reachable_tail_certificate

def run():
    n=np.array([[5.,3.,2.],[7.,1.,6.]])
    p=np.array([[9.,8.],[4.,2.]])
    target=np.zeros_like(n);reservoir=p+n[:,1:];alpha=np.array([.2,.1]);h=.25
    q=dict(recombination_m3_s=alpha,ionization_s_inv=[0.,0.],heater_ionization_per_J=[1.,2.],chemical_recovery_efficiency=.5)
    cur=n.copy();pool=p.copy();worst=0.
    for k in range(1,65):
        for i in range(2):
            r,a,pool[i]=reaction(cur[i],pool[i],1000.,0.,h,q)
            assert np.all(a==0.)
            cur[i]=cur[i]-r
        b=recombination_tail_geometry(n,target,p,reservoir,alpha,h,k)
        upper=np.asarray(b['electron_upper_m3'])
        assert np.all(cur[:,0]<=upper)
        assert np.linalg.norm(cur)<=b['population_norm_upper']
        assert np.linalg.norm(pool-reservoir)<=b['pool_norm_upper']
        worst=max(worst,float(np.max(cur[:,0]/upper)))
    assert b['asymptotic_population_return'] and b['finite_positive_population_exact_return_obstructed']
    wrong=recombination_tail_geometry(n,n,p,p,alpha,h,64)
    assert wrong['nonzero_initial_population_limit_obstructed']
    x=np.array([1.,0.,0.])
    tail=source_off_tail_receipt(x,n,p,np.array([1.,2.]),target,reservoir,np.ones(2),np.ones(3),np.ones(2),np.ones(2),q,h,64)
    assert tail['work']['additional_useful_upper_J']==.5
    assert tail['work']['additional_net_upper_J']==12.5
    assert not tail['asymptotic_full_return_admitted']
    bad=dict(q,ionization_s_inv=[0.,.1])
    assert source_off_tail_receipt(x,n,p,np.ones(2),target,reservoir,np.ones(2),np.ones(3),np.ones(2),np.ones(2),bad,h,64)['status']=='BASELINE_IONIZATION_PREVENTS_BIRTH_FREE_TAIL'
    mesh=dict(positions_m=[[0,0,0],[1,0,0],[2,0,0]],coordinate_site=[0,1,2],
        faces=[dict(id='a',source=0,target=1,normal=[1,0,0],area_m2=1)],front_speed_m_s=100.)
    H=np.array([[-1.,-2.,0.],[2.,0.,0.],[0.,0.,0.]])
    y,receipt=timed_step(x,H,np.zeros(3),h,mesh)
    T=tail_stage_matrix(H,h,receipt)
    assert np.allclose(y,np.array(T*S.Matrix([1,0,0]),float).ravel())
    stable=reachable_tail_certificate(T,S.Matrix([1,0,0]))
    assert stable['field_return_proved'] and stable['reachable_rank']==2
    assert stable['block_steps']==2 and stable['rho_squared']=='31/32'
    invariant=reachable_tail_certificate(T,S.Matrix([1,0,1]))
    assert invariant['exact_zero_return_obstructed'] and not invariant['field_return_proved']
    _,forced=timed_step(x,H,np.array([.1,0,0]),h,mesh)
    try:tail_stage_matrix(H,h,forced)
    except ValueError:pass
    else:raise AssertionError('forced tail admitted')
    print(dict(status='ASYMPTOTIC_TAIL_PASS',reaction_steps=64,max_bound_ratio=worst,
        terminal_electron_upper=b['electron_upper_m3'],stable=stable,invariant=invariant,
        tail_work_upper=tail['work']['additional_net_upper_J'],physical_admission=False))
if __name__=='__main__':run()
