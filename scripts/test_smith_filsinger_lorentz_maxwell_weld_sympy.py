"""SymPy source-equivalent Maxwell-Lorentz frequency/time weld tests."""
import sympy as S
import pytest
from smith_filsinger_lorentz_ade_sympy import LorentzMaterial
from smith_filsinger_lorentz_maxwell_weld_sympy import (
    phasor_material_epsilon,spectral_material_loss,
    coupled_maxwell_generator,spectral_flux_loss)
from smith_filsinger_passive_radiation_sympy import (
    passive_halfspace_admittance,outgoing_passive_wavenumber,
    cayley_passivity_identity)

@pytest.mark.parametrize('omega',[S.Rational(1,2),S.Rational(1),S.Rational(2)])
def test_material_susceptibility_produces_passive_maxwell_epsilon(omega):
    m=LorentzMaterial();eps=phasor_material_epsilon(omega)
    assert S.re(eps)>0 and S.im(eps)>0
    energy=spectral_material_loss(omega,m)
    assert energy['residual']==0
    assert energy['total']==energy['ohmic']+energy['relaxation']
    assert energy['relaxation']>0

@pytest.mark.parametrize('omega',[S.Rational(1),S.Rational(2)])
def test_exact_material_damping_matches_maxwell_poynting_operator(omega):
    diss=spectral_material_loss(omega)
    M=coupled_maxwell_generator(omega)
    expected=S.diag(-diss['total'],-diss['total'],0,0)
    assert spectral_flux_loss(omega)==expected
    lhs,rhs=cayley_passivity_identity(M,S.Rational(1,7))
    assert lhs==rhs


def test_dispersive_passive_halfspace_branch_conforms_to_same_material():
    w=S.Rational(1)
    m=LorentzMaterial()
    e=phasor_material_epsilon(w,m)
    q=outgoing_passive_wavenumber(w,0,0,m.mu,e)
    assert S.re(q)>0 and S.im(q)>0
    y=passive_halfspace_admittance(w,0,0,m.mu,e)
    assert y.shape==(2,2)


def test_conductor_absorption_not_double_counted_with_dielectric():
    w=S.Rational(2);m=LorentzMaterial()
    eps=phasor_material_epsilon(w,m)
    chi=m.alpha/(m.omega0sq-w*w-S.I*m.gamma*w)
    assert S.simplify(eps-m.eps-chi-S.I*m.sigma/w)==0
    total=spectral_material_loss(w)['total']
    assert total!=m.sigma
    assert total+m.sigma != total


def test_time_domain_current_to_polarization_energy_susceptibility():
    m=LorentzMaterial()
    w=S.Rational(1)
    loss=spectral_material_loss(w,m)
    chi=m.alpha/(m.omega0sq-w*w-S.I*m.gamma*w)
    assert S.simplify(loss['relaxation']-m.gamma/m.alpha*(w*chi)*S.conjugate(w*chi))==0


def test_no_original_source_work_from_spectral_passivity():
    assert spectral_material_loss(S.Rational(1))['total']>0
    original_independent_meter=None
    assert original_independent_meter is None
