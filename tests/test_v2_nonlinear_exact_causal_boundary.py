"""Exact nonlinear causal multi-winding generator theorem: positive + adversarial."""
from fractions import Fraction as F
import importlib.util
from pathlib import Path
import numpy as np
import sympy as sp
import pytest

src=Path(__file__).resolve().parents[1]/'scripts'/'v2_nonlinear_exact_causal_boundary.py'
spec=importlib.util.spec_from_file_location('v2_nonlinear_exact',src)
m=importlib.util.module_from_spec(spec)
import sys
sys.modules[spec.name]=m
spec.loader.exec_module(m)

@pytest.mark.parametrize('phase',(2,3,4,6,9,12))
def test_polynomial_avf_all_state_secant_exact(phase):
    p=m.P(m=phase)
    A=m.A_matrix(p,2)
    for shift in (0,1,2):
        lam0=[F(j-3+shift,5) for j in range(phase)]
        lam1=[F(2*j-4-shift,7) for j in range(phase)]
        z0=[F(j+shift,11) for j in range(phase)]
        z1=[F(-j-1,13) for j in range(phase)]
        assert m.secant(p,A,lam0,z0,lam1,z1)

@pytest.mark.parametrize('phase',(2,3,4))
def test_symbolic_polynomial_identity_for_general_reciprocal_mutual_matrix(phase):
    assert m.nonlinear_identity_symbolic(phase)['polynomial_identity_residual']=='0'

@pytest.mark.parametrize('phase',(2,3,4,6,9,12))
@pytest.mark.parametrize('delay_cells',(1,2,3))
def test_manufactured_orbit_is_exact_for_every_port_and_closed_cycle(phase,delay_cells):
    p=m.P(m=phase,n=delay_cells)
    c=m.periodic_manufacture(p,clock_shift=2)
    assert c['states'][0]!=tuple(F(0) for _ in c['states'][0])
    assert c['work']['source']+c['work']['rotor_param']==c['work']['line_loss']+c['work']['copper']+c['work']['memory']
    assert c['work']['copper']>0 and c['work']['memory']>0 and c['work']['line_loss']>0
    assert m.numeric_replay(p,c)<3e-11

@pytest.mark.parametrize('phase',(2,3,4,6,9,12))
def test_local_nonlinear_periodic_contractivity_rational_not_numeric_guess(phase):
    p=m.P(m=phase,s=F(999,1000),R=F(1,100),Z=F(1,2))
    c=m.periodic_manufacture(p,clock_shift=2)
    q=m.local_attractor(p,c,power=1)
    assert F(q['iterate_inf_norm']) < 1
    assert q['locally_attracting']

@pytest.mark.parametrize('phase',(3,8))
def test_generator_sign_control_requires_positive_rotor_work(phase):
    p=m.P(m=phase,s=F(999,1000),R=F(1,100),Z=F(1,2))
    c=m.periodic_manufacture(p,clock_shift=2)
    assert c['work']['source']<0 and c['work']['rotor_param']>0
    exported=-c['work']['source']
    assert exported+c['work']['copper']+c['work']['memory']+c['work']['line_loss']==c['work']['rotor_param']
    assert c['work']['line_loss']>0

@pytest.mark.parametrize('delay_cells',(1,2,3,5))
def test_true_oneway_and_roundtrip_flight_of_nontrivial_nonlinear_signal(delay_cells):
    p=m.P(m=2,n=delay_cells)
    A=m.A_matrix(p,0)
    x=np.zeros(p.state_dim); quiet=np.zeros(p.state_dim)
    terminal=[];returned=[]
    for k in range(2*delay_cells+2):
        j=2*p.m*p.n
        terminal.append(np.max(np.abs(x[j:j+p.m]-quiet[j:j+p.m])))
        returned.append(max(abs(float(p.s)*(x[p.m*delay_cells+a*delay_cells]-quiet[p.m*delay_cells+a*delay_cells])) for a in range(p.m)))
        u=[1.,0.] if k==0 else [0.,0.]
        x,_=m.numeric_step(p,A,x,u)
        quiet,_=m.numeric_step(p,A,quiet,[0.,0.])
    assert all(v<1e-12 for v in terminal[:delay_cells+1])
    assert terminal[delay_cells+1]>1e-6
    assert all(v<1e-12 for v in returned[:2*delay_cells])
    assert returned[2*delay_cells]>1e-6

@pytest.mark.parametrize('phase',(2,3,5))
def test_implicit_step_from_arbitrary_rational_endpoint_exact(phase):
    p=m.P(m=phase,n=2)
    A=m.A_matrix(p,0)
    lam0=[F(k+1,7) for k in range(phase)]
    lam1=[F(k+3,9) for k in range(phase)]
    z0=[F(2*k-3,11) for k in range(phase)]
    alpha=(1-p.dt*p.mu*p.h/2)/(1+p.dt*p.mu*p.h/2)
    coeff=p.dt*p.mu*p.g/2/(1+p.dt*p.mu*p.h/2)
    z1=[alpha*z0[k]+coeff*(lam0[k]+lam1[k]) for k in range(phase)]
    i,_=m.avf_grad(p,A,lam0,z0,lam1,z1)
    a=[(lam1[k]-lam0[k])/p.dt/2+(p.Z+p.R)*i[k]/2 for k in range(phase)]
    f=[];b=[]
    for k in range(phase):f.extend((F(-1,3),a[k]/p.s))
    for k in range(phase):b.extend((F(k+1,5),F(-k,7)))
    state=m.pack(f,b,lam0,z0)
    u=tuple(F(k-1,4) for k in range(phase))
    end,work=m.step_from_end(p,A,state,u,lam1,z1)
    assert work['residual']==0
    got,error=m.numeric_step(p,A,np.array(state,float),np.array(u,float))
    assert error<1e-10
    assert np.max(np.abs(got-np.array(end,float)))<1e-9

@pytest.mark.parametrize('bad',[
    {'n':0}, {'m':1},{'dt':F(0)},{'Z':F(0)}, {'s':F(0)},
    {'s':F(11,10)},{'R':F(0)},{'mu':F(0)},
    {'speed':F(m.C+1)},{'speed':F(-1)},{'quartic':F(0)}])
def test_invalid_physical_parameter_fails_closed(bad):
    with pytest.raises(ValueError):m.P(**bad).check()

def test_nonreciprocal_and_nonconvex_material_fail_closed():
    p=m.P()
    with pytest.raises(ValueError):p.check(((F(1),F(1,8)),(F(0),F(1))))
    with pytest.raises(ValueError):p.check(((F(1,10),F(1)),(F(1),F(1,10))))

def test_nonzero_mechanical_jump_cannot_be_relabelled_free_energy():
    p=m.P(m=3)
    c=m.periodic_manufacture(p,clock_shift=2)
    assert c['work']['rotor_param']!=0
    assert c['work']['source']-(c['work']['line_loss']+c['work']['copper']+c['work']['memory'])==-c['work']['rotor_param']

def test_exact_jacobian_matches_independently_nonlinear_implicit_finite_difference():
    p=m.P(m=2,n=1)
    c=m.periodic_manufacture(p)
    x=np.array(c['states'][0],float)
    A=c['A'][0]
    u=np.array(c['launches'][0],float)
    J=np.array(m.step_jacobian(p,A,c['states'][0],c['states'][1]),float)
    eps=2e-6
    for k in range(p.state_dim):
        e=np.zeros(p.state_dim);e[k]=eps
        plus,_=m.numeric_step(p,A,x+e,u)
        minus,_=m.numeric_step(p,A,x-e,u)
        assert np.max(np.abs((plus-minus)/(2*eps)-J[:,k]))<2e-7

def test_realistic_half_metre_flight_is_not_abstract_orbit_clock():
    p=m.P()
    # The abstract exact periodic witness has a huge implicit cable length.
    assert float(p.length)>4e7
    # A physical 0.5m / 0.7c flight is a few nanoseconds, not one 0.25s tick.
    speed=F(7,10)*m.C
    flight=F(1,2)/speed
    assert F(2,10**9) < flight < F(3,10**9)
    assert flight < p.dt/10_000_000

def test_new_scoped_status_does_not_claim_full_v2_or_maxwell():
    r=m.run()
    assert r['periodic_endpoint_exact']
    assert F(r['periodic_work']['source'])<0
    assert F(r['periodic_work']['rotor_param'])>0
    assert F(r['local_attractor']['iterate_inf_norm'])<1
    assert len(r['open'])>=6

@pytest.mark.parametrize('ticks',(4,8,16,32,128))
def test_smooth_rotor_parameter_work_endpoint_bound_positive(ticks):
    # Analytic 2-winding A(t)=scalar(t)*I, smooth lambda(t), no claim the
    # waveform solves the physical V2 coupled current equations.
    import math
    W=13.0
    T=2*math.pi/W
    amp=.16
    base=np.array([1.1,-.3]);osc=np.array([.3,.15])
    def lam(t):return base+osc*np.sin(W*t+.17)
    def A(t):return 1.0+amp*np.sin(W*t)
    times=np.linspace(0,T,100001)
    continuous=np.trapezoid([.5*float(lam(t)@lam(t))*amp*W*math.cos(W*t) for t in times],times)
    clock=np.linspace(0,T,ticks+1)
    discrete=sum(.5*float(lam(clock[k+1])@lam(clock[k+1]))*(A(clock[k+1])-A(clock[k])) for k in range(ticks))
    B=float(np.linalg.norm(base)+np.linalg.norm(osc))
    D=float(W*np.linalg.norm(osc))
    # TV(A) = 4amp over the full period; the simple amp*W*T bound is conservative.
    bound=m.clocked_rotor_work_error_bound(B,D,T/ticks,4*amp)
    assert abs(continuous-discrete)<bound+1e-8
    assert bound>0

@pytest.mark.parametrize('bad',[(1.,-1.,.1,1.),(1.,1.,0.,1.),(1.,1.,.1,float('inf'))])
def test_smooth_rotor_approximation_requires_lipschitz_inputs(bad):
    with pytest.raises(ValueError):m.clocked_rotor_work_error_bound(*bad)
