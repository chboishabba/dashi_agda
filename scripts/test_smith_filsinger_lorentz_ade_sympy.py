"""Exact unit tests for the canonical source/material ledger producer.

All fixtures are mathematical, NOT observed solar or original electrode data.
"""
from dataclasses import replace
import sympy as S
import pytest
from smith_filsinger_lorentz_ade_sympy import (
    LorentzMaterial,curl_matrix,generator,energy,exact_midpoint,
    susceptibility_laplace,epsilon_effective_laplace,
    polarization_convolution_coefficients,phasor_passivity)

@pytest.mark.parametrize('n',[1,2,3])
def test_passive_matrix_storage_identity(n):
    A,B,M=generator(n)
    N=S.simplify(A.T*M+M*A)
    material=LorentzMaterial()
    expected=S.diag(*([-2*material.sigma]*n+[0]*n+[0]*n+
                     [-2*material.gamma/material.alpha]*n))
    assert N==expected
    assert M==M.T
    assert all(M[i,i]>0 for i in range(M.rows))

@pytest.mark.parametrize('n',[1,2,3])
def test_exact_one_step_nonzero_source_ion_memory(n):
    A,B,M=generator(n)
    z=S.zeros(4*n,1)
    jn=S.Matrix([S.Rational(j+1,3) for j in range(n)])
    jc=S.Matrix([S.Rational((-1)**j,5) for j in range(n)])
    r=exact_midpoint(z,jn,jc,S.Rational(1,7),A,B,M)
    assert r['residual']==0
    assert r['ohmic']>0 and r['relaxation']>0
    assert r['energy_change']==(r['natural_work']+r['controller_work']
                                  -r['ohmic']-r['relaxation'])
    assert r['z'][3*n:4*n,:]!=S.zeros(n,1)

@pytest.mark.parametrize('steps',[1,2,4])
def test_iterated_exact_closed_curl_energy(steps):
    A,B,M=generator(2)
    z=S.zeros(8,1);start=energy(z,M)
    net=S.Integer(0)
    for k in range(steps):
        jn=S.Matrix([S.Rational(k+1,2),S.Rational(-1,3)])
        jc=S.Matrix([S.Rational(1,4),S.Rational(0)])
        r=exact_midpoint(z,jn,jc,S.Rational(1,6),A,B,M)
        net+=r['natural_work']+r['controller_work']-r['ohmic']-r['relaxation']
        z=r['z']
    assert S.factor(energy(z,M)-start-net)==0

@pytest.mark.parametrize('s',[S.Rational(1,2),S.Rational(2),S.Rational(5,3)])
def test_exact_susceptibility_from_eliminated_polarization(s):
    m=LorentzMaterial()
    chi=susceptibility_laplace(s,m)
    assert S.factor(chi*(s*s+m.gamma*s+m.omega0sq)-m.alpha)==0
    assert S.factor(epsilon_effective_laplace(s,m)
                    -m.eps-m.sigma/s-chi)==0
    A,B,M=generator(1)
    G=(s*S.eye(4)-A).inv()*B
    # E(s)=[epsilon*s+sigma+alpha*s/(s²+gamma*s+w0²)+C²/(mu*s)]^-1 * J
    adm=s*epsilon_effective_laplace(s,m)+1/(m.mu*s)
    assert S.factor(G[0,0]-1/adm)==0
    assert S.factor(G[2,0]-chi*G[0,0])==0

@pytest.mark.parametrize('omega',[S.Rational(1,2),S.Rational(2),S.Rational(5,3)])
def test_phasor_loss_nonnegative(omega):
    chi,loss=phasor_passivity(omega)
    m=LorentzMaterial()
    explicit=(m.alpha*m.gamma*omega/
         ((m.omega0sq-omega**2)**2+(m.gamma*omega)**2))
    assert S.factor(loss-explicit)==0
    assert loss>0


def test_zero_source_stays_zero_no_solar_power():
    A,B,M=generator(2)
    z=S.zeros(8,1);zero=S.zeros(2,1)
    r=exact_midpoint(z,zero,zero,S.Rational(1,6),A,B,M)
    assert r['z']==z
    assert all(r[k]==0 for k in ('natural_work','controller_work',
                                'ohmic','relaxation','energy_change','residual'))


def test_material_memory_free_field_reacts_and_dissipates():
    A,B,M=generator(2)
    z=S.zeros(8,1);z[6]=S.Rational(1)
    zero=S.zeros(2,1)
    r=exact_midpoint(z,zero,zero,S.Rational(1,7),A,B,M)
    assert r['natural_work']==r['controller_work']==0
    assert r['energy_change']<0
    assert r['ohmic']>=0 and r['relaxation']>0


def test_active_negative_gamma_rejected():
    with pytest.raises(ValueError):generator(material=replace(LorentzMaterial(),gamma=-1))
    with pytest.raises(ValueError):generator(material=replace(LorentzMaterial(),sigma=-1))


def test_wrong_polarization_energy_account_rejected():
    A,B,M=generator(1)
    z=S.zeros(4,1);r=exact_midpoint(z,S.Matrix([1]),S.Matrix([0]),
                                  S.Rational(1,5),A,B,M)
    bad=M.copy();bad[3,3]=0  # silently discard polarization kinetic store
    error=S.factor(energy(r['z'],bad)-energy(z,bad)-r['natural_work']
                   -r['controller_work']+r['ohmic']+r['relaxation'])
    assert error!=0


def test_no_future_source_used_by_midpoint():
    A,B,M=generator(1);zero=S.zeros(4,1)
    j=S.Matrix([1]);ctrl=S.Matrix([0])
    first=exact_midpoint(zero,j,ctrl,S.Rational(1,7),A,B,M)['z']
    assert first==exact_midpoint(zero,j,ctrl,S.Rational(1,7),A,B,M)['z']


def test_analytic_impulse_derivative_at_zero():
    m=LorentzMaterial();coeff=polarization_convolution_coefficients(m)
    assert coeff==[0,m.alpha,-m.alpha*m.gamma,
                   m.alpha*(m.gamma**2-m.omega0sq)]


def test_underdamped_material_poles_stable():
    from smith_filsinger_lorentz_ade_sympy import lorentz_poles
    m=LorentzMaterial();roots=lorentz_poles(m)
    for pole in roots:
        assert S.simplify(S.re(pole))==-m.gamma/2<0
        assert S.simplify(pole*pole+m.gamma*pole+m.omega0sq)==0


def test_causal_impulse_and_exact_material_ode():
    from smith_filsinger_lorentz_ade_sympy import retarded_impulse
    m=LorentzMaterial();t=S.symbols('t',positive=True)
    g=retarded_impulse(t,m)
    residual=S.simplify(S.diff(g,t,2)+m.gamma*S.diff(g,t)
                        +m.omega0sq*g)
    assert residual==0
    assert S.simplify(g.subs(t,0))==0
    assert S.simplify(S.diff(g,t).subs(t,0))==m.alpha
    assert retarded_impulse(S.Rational(-1,2),m)==0
    assert retarded_impulse(S.Rational(0),m)==0


def test_material_impulse_matches_laplace_susceptibility():
    from smith_filsinger_lorentz_ade_sympy import retarded_impulse
    t=S.symbols('t',positive=True);s=S.symbols('s',positive=True)
    g=retarded_impulse(t)
    laplace=S.integrate(S.exp(-s*t)*g,(t,0,S.oo))
    assert S.simplify(laplace-susceptibility_laplace(s))==0


def test_no_fake_material_light_cone_from_local_ode():
    from smith_filsinger_lorentz_ade_sympy import retarded_impulse
    assert retarded_impulse(S.Rational(1,10))!=0
    assert retarded_impulse(S.Rational(-1,10))==0


def test_undamped_or_unstable_is_not_certified_as_dissipative():
    from smith_filsinger_lorentz_ade_sympy import lorentz_poles
    with pytest.raises(ValueError):lorentz_poles(replace(LorentzMaterial(),gamma=0))
    with pytest.raises(ValueError):lorentz_poles(replace(LorentzMaterial(),gamma=5))


@pytest.mark.parametrize('n',[1,2,3])
def test_actual_useful_load_separate_from_ohmic_material_losses(n):
    g=S.Rational(3,7)
    A,B,M=generator(n,load_conductance=g)
    z=S.zeros(4*n,1)
    source=S.Matrix([S.Rational(j+1,2) for j in range(n)])
    ctrl=S.Matrix([S.Rational(1,5) for j in range(n)])
    r=exact_midpoint(z,source,ctrl,S.Rational(1,8),A,B,M,
                     load_conductance=g)
    assert r['residual']==0
    assert r['useful_load']>0 and r['ohmic']>0 and r['relaxation']>0
    assert S.factor(r['energy_change'] + r['useful_load']+r['ohmic']
        +r['relaxation']-r['natural_work']-r['controller_work'])==0


def test_invented_useful_load_without_conductance_fails():
    A,B,M=generator(1,load_conductance=S.Rational(1,4))
    z=S.zeros(4,1)
    with pytest.raises(ValueError):
        exact_midpoint(z,S.Matrix([1]),S.Matrix([0]),S.Rational(1,8),
                       A,B,M,load_conductance=S.Rational(3))


def test_source_off_storage_can_pay_load_transiently_but_not_repeatably():
    g=S.Rational(1,2)
    A,B,M=generator(1,load_conductance=g)
    z=S.Matrix([S.Rational(1),0,0,0])
    zero=S.Matrix([0]);u0=energy(z,M)
    r=exact_midpoint(z,zero,zero,S.Rational(1,4),A,B,M,
                     load_conductance=g)
    assert r['useful_load']>0
    assert r['energy_change']==-(r['useful_load']+r['ohmic']+r['relaxation'])
    assert energy(r['z'],M)<u0


def test_load_omission_breaks_full_source_balance():
    g=S.Rational(1,3);A,B,M=generator(1,load_conductance=g)
    z=S.zeros(4,1);r=exact_midpoint(z,S.Matrix([1]),S.Matrix([0]),
        S.Rational(1,5),A,B,M,load_conductance=g)
    assert r['residual']==0
    assert (S.factor(r['energy_change']-r['natural_work']
                    -r['controller_work']+r['ohmic']+r['relaxation'])
            == -r['useful_load'])


def test_exact_five_step_closed_material_and_field_cycle_from_supplied_source():
    from smith_filsinger_lorentz_ade_sympy import synthetic_cycle_work_receipt
    A,B,M=generator(1,load_conductance=S.Rational(1,3))
    h=S.Rational(1,5); ident=S.eye(4)
    transition=(ident-h*A/2).inv()*(ident+h*A/2)
    impulse=(ident-h*A/2).inv()*h*B
    z0=S.Matrix([1,0,0,0])
    sources=S.symbols('j0:5')
    zend=transition**5*z0
    for i,j in enumerate(sources):
        zend += transition**(4-i)*impulse*j
    solved=S.solve(list(zend-z0),sources[:-1],dict=True)
    assert len(solved)==1
    jvals=[S.simplify(solved[0][j].subs(sources[-1],1)) for j in sources[:-1]]+[S.Integer(1)]
    z=z0;steps=[]
    for j in jvals:
        receipt=exact_midpoint(z,S.Matrix([j]),S.Matrix([0]),h,A,B,M,
                               load_conductance=S.Rational(1,3))
        steps.append(receipt);z=receipt['z']
    audit=synthetic_cycle_work_receipt(z0,steps,M)
    assert audit['restored_all_4n_states']
    assert audit['storage_delta']==0
    assert audit['conservation_residual']==0
    assert audit['useful_load']>0 and audit['ohmic_loss']>0
    assert audit['natural_work']==(audit['useful_load']+
                                    audit['ohmic_loss']+audit['relaxation_loss'])
    assert not audit['physically_replenished_source_certified']


def test_energy_return_is_not_full_state_restoration():
    from smith_filsinger_lorentz_ade_sympy import synthetic_cycle_work_receipt
    A,B,M=generator(1,load_conductance=S.Rational(1,4))
    z=S.Matrix([1,0,0,0]);step=exact_midpoint(z,S.Matrix([1]),S.Matrix([0]),
       S.Rational(1,5),A,B,M,load_conductance=S.Rational(1,4))
    audit=synthetic_cycle_work_receipt(z,[step],M)
    assert not audit['restored_all_4n_states']
    assert audit['conservation_residual']==0
    assert not audit['original_source_meter_present']


def test_nonconsecutive_source_trace_is_rejected():
    from smith_filsinger_lorentz_ade_sympy import synthetic_cycle_work_receipt
    A,B,M=generator(1);start=S.zeros(4,1)
    r=exact_midpoint(start,S.Matrix([1]),S.Matrix([0]),S.Rational(1,5),A,B,M)
    with pytest.raises(ValueError,match='nonconsecutive'):
        synthetic_cycle_work_receipt(start,[r,r],M)
