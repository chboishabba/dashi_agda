"""Local paid terminal material return: nonzero field is never erased."""
import numpy as np
import sympy as S
from solar_controlled_terminal_return import local_return

def run():
    n=np.array([[5.,3.,2.],[4.,1.,3.]])
    n0=np.array([[3.,1.,2.],[5.,3.,2.]])
    p=np.array([[10.,10.],[10.,10.]])
    p0=p+n[:,1:]-n0[:,1:]
    x=np.linspace(-.2,.2,20);t=np.array([1.,2.]);V=np.ones(2);C=np.array([2.,3.]);chem=np.array([.01,.02,.03])
    q=dict(chemical_input_efficiency=.8,chemical_recovery_efficiency=.5)
    policy=dict(removed_limit_m3=np.full((2,3),10.),created_limit_m3=np.full((2,3),10.),
        cooling_limit_J=np.full(2,10.),cooling_COP=np.full(2,2.),birth_velocity_m_s=np.zeros((2,3,3)),
        extra_actuator_work_J=.5,gross_paid_budget_J=10.)
    state,w=local_return(x,n,p,t,n0,p0,V,C,chem,q,policy)
    assert np.array_equal(state[1],n0) and np.array_equal(state[2],p0) and np.array_equal(state[3],[0.,0.])
    assert np.array_equal(state[0][:2],x[:2]) and np.linalg.norm(state[0])>0
    assert w['electromagnetic_cochains_unchanged'] and w['cooling_work_J']==4.
    assert abs(w['balance_J'])<1e-12 and w['gross_paid_J']>4.5
    assert w['removed_m3']==[[2.,2.,0.],[1.,0.,1.]]
    assert w['created_m3']==[[0.,0.,0.],[2.,2.,0.]]
    for j in range(2):
        for k in range(3):
            a=S.Rational(w['created_m3'][j][k]);r=S.Rational(w['removed_m3'][j][k])
            assert a+r==abs(S.Rational(n0[j,k]-n[j,k])) if k>0 else a+r>=abs(S.Rational(n0[j,k]-n[j,k]))
    bad=[dict(policy,gross_paid_budget_J=.1),dict(policy,cooling_limit_J=[0.,0.]),
         dict(policy,removed_limit_m3=np.zeros((2,3))),dict(policy,created_limit_m3=np.zeros((2,3)))]
    for case in bad:
        try:local_return(x,n,p,t,n0,p0,V,C,chem,q,case)
        except ValueError:pass
        else:raise AssertionError('unpaid or capacity-exceeding controller admitted')
    try:local_return(x,n,p,t,n0,p0+1.,V,C,chem,q,policy)
    except ValueError:pass
    else:raise AssertionError('forged inventory admitted')
    print(dict(status='CONTROLLED_MATERIAL_RETURN_PASS',gross_paid_J=w['gross_paid_J'],
        net_paid_J=w['net_paid_J'],balance_J=w['balance_J'],remaining_field_norm=float(np.linalg.norm(state[0])),
        invalid_cases_rejected=5,physical_admission=False))
if __name__=='__main__':run()
