"""F13/F15 exact SymPy checks. Passing != physical original-world closure."""
import sympy as S
import pytest
from smith_filsinger_layered_green_sympy import (
    matrices,admittance,green_laplace,terminal_transfer,midpoint_step,
    restored_cycle_audit,uncertainty_gain_certificate)

@pytest.fixture(scope="module")
def m():return matrices()

@pytest.mark.parametrize("s",[S.Rational(1,2),S.Rational(1),S.Rational(2),S.Rational(7,3)])
def test_green_six_component_both_inverses(m,s):
    A=admittance(s,*m); G=green_laplace(s,*m)
    assert A*G==S.eye(6) and G*A==S.eye(6)
    assert terminal_transfer(G)!=0

def test_hall_reversal_changes_transfer_but_preserves_transpose_dual(m):
    C,P,H,K=m;s=S.Rational(2)
    assert H.T==-H
    gp=green_laplace(s,C,P,H,K)
    gm=green_laplace(s,C,P,-H,K)
    assert gp.T==gm and gp!=gm

def test_exact_positive_symmetric_part(m):
    C,P,H,K=m;s=S.Rational(3,2)
    A=admittance(s,*m)
    B=(A+A.T)/2
    assert B==s*s*C+s*P+K
    assert all(B[:j,:j].det()>0 for j in range(1,7))

@pytest.mark.parametrize("steps",[1,2,3])
def test_implicit_midpoint_hall_zero_work_exact_energy(m,steps):
    C,P,H,K=m
    e=S.zeros(6,1);v=S.zeros(6,1)
    for n in range(steps):
        natural=S.zeros(6,1);ctrl=S.zeros(6,1)
        natural[4]=S.Rational(3+n,2)
        natural[5]=S.Rational(-1,5)
        ctrl[2]=S.Rational(2,3)
        z=midpoint_step(e,v,natural,ctrl,*m)
        assert z['hall_work']==0 and z['residual']==0
        assert z['heat']>=0
        assert z['energy_change']==z['natural_work']+z['controller_work']-z['heat']
        e,v=z['e'],z['v']

def test_present_source_no_future_source_needed(m):
    e=S.zeros(6,1);v=S.zeros(6,1)
    j=S.zeros(6,1);j[4]=1
    z=midpoint_step(e,v,j,S.zeros(6,1),*m)
    assert z['e']!=S.zeros(6,1)
    assert z['e']==midpoint_step(e,v,j,S.zeros(6,1),*m)['e']

def test_symbolic_two_polarization_hall_inverse():
    a,h=S.symbols('a h',real=True,nonzero=True)
    A=S.Matrix([[a,h],[-h,a]])
    G=S.Matrix([[a,-h],[h,a]])/(a*a+h*h)
    assert S.simplify(A*G)==S.eye(2)
    z=S.Matrix(S.symbols('u v'))
    assert S.expand((z.T*(A-A.T)*z)[0])==0

def test_hypothetical_positive_metered_hundredfold_is_only_conditional():
    data=dict(natural=100,controller=1,load=100,loss=1,initial_storage=5,final_storage=5)
    assert restored_cycle_audit(**data)['status']=='OPEN'
    out=restored_cycle_audit(**data,independent_natural_meter=True,
        independent_load_meter=True,original_terminal_calibration=True)
    assert out['status']=='CONDITIONAL_LEDGER_PASS'
    assert out['hundredfold_load_over_controller']

def test_source_free_storage_depletion_rejected():
    out=restored_cycle_audit(natural=0,controller=1,load=10,loss=0,
        initial_storage=9,final_storage=0,independent_natural_meter=True,
        independent_load_meter=True,original_terminal_calibration=True)
    assert out['status']=='REJECT'

def test_double_counted_incoming_boundary_rejected():
    out=restored_cycle_audit(natural=100,controller=1,load=100,loss=1,
        initial_storage=0,final_storage=0,independent_natural_meter=True,
        independent_load_meter=True,original_terminal_calibration=True,
        double_counted_boundary=True)
    assert out['status']=='REJECT'

def test_false_hundredfold_with_no_source_rejected():
    out=restored_cycle_audit(natural=0,controller=1,load=100,loss=0,
        initial_storage=0,final_storage=0,independent_natural_meter=True,
        independent_load_meter=True,original_terminal_calibration=True)
    assert out['status']=='REJECT'

def interval_fixture():
    return dict(natural_interval=(100,102),controller_interval=(1,S.Rational(11,10)),
        load_interval=(100,101),loss_interval=(0,2),storage_change_interval=(0,0),
        independent_source=True,same_original_terminals=True)

def test_lower_uncertainty_gain_not_nominal():
    d=interval_fixture()
    a=uncertainty_gain_certificate(**d)
    assert a['status']=='CONDITIONAL_INTERVAL_CERTIFICATE'
    assert a['robust_load_over_controller_lower']==S.Rational(1000,11)
    assert not a['hundredfold_robust']
    d['controller_interval']=(S.Rational(1,2),S.Rational(1))
    assert uncertainty_gain_certificate(**d)['hundredfold_robust']

def test_inconsistent_measured_work_rejected():
    d=interval_fixture();d['natural_interval']=(0,0);d['controller_interval']=(1,1)
    d['load_interval']=(100,100);d['loss_interval']=(0,0)
    assert uncertainty_gain_certificate(**d)['status']=='REJECT'

def test_unrestored_or_missing_source_fails_closed():
    d=interval_fixture();d['storage_change_interval']=(0,1)
    assert uncertainty_gain_certificate(**d)['status']=='OPEN'
    d=interval_fixture();d['independent_source']=False
    assert uncertainty_gain_certificate(**d)['status']=='OPEN'

@pytest.mark.parametrize("k2",[S.Rational(0),S.Rational(1,3),S.Rational(2),S.Rational(7,2)])
def test_four_nonzero_transverse_fourier_modes_exact(k2):
    model=matrices(k_parallel_squared=k2)
    C,P,H,K=model
    s=S.Rational(3,2)
    A=admittance(s,*model)
    G=green_laplace(s,*model)
    assert A*G==S.eye(6) and G*A==S.eye(6)
    assert H.T==-H
    assert terminal_transfer(G)!=0
    B=(A+A.T)/2
    assert all(B[:j,:j].det()>0 for j in range(1,7))

def test_transverse_mode_response_changes_with_k_squared():
    s=S.Rational(2)
    g0=green_laplace(s,*matrices(k_parallel_squared=0))
    g2=green_laplace(s,*matrices(k_parallel_squared=2))
    assert g0!=g2
    assert terminal_transfer(g0)!=terminal_transfer(g2)

def test_negative_transverse_spectral_mode_rejected():
    with pytest.raises(ValueError):matrices(k_parallel_squared=-1)
