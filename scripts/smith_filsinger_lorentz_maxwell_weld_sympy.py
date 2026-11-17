"""Connect the SAME passive Lorentz susceptibility to existing oblique
Maxwell and passive radiation source Green. No original parameter evidence.
"""
import sympy as S
from smith_filsinger_lorentz_ade_sympy import (
    LorentzMaterial, epsilon_effective_laplace, susceptibility_laplace)
from smith_filsinger_oblique_maxwell_sympy import oblique_generator
from smith_filsinger_passive_radiation_sympy import (
    outgoing_passive_wavenumber, passive_halfspace_admittance,
    cayley_passivity_identity)
from smith_filsinger_radiation_green_sympy import F


def phasor_material_epsilon(omega,material=None):
    """exp(-iωt) passive dispersive epsilon: sigma is included ONCE."""
    m=(material or LorentzMaterial()).validated()
    w=S.sympify(omega)
    if w.is_positive is not True:raise ValueError('omega>0 needed')
    return S.simplify(epsilon_effective_laplace(-S.I*w,m))


def spectral_material_loss(omega,material=None):
    """omega Im eps = ohmic sigma + Lorentz relaxation gamma/alpha |v/E|²"""
    m=(material or LorentzMaterial()).validated()
    w=S.sympify(omega)
    if w.is_positive is not True:raise ValueError('omega>0 needed')
    chi=S.simplify(susceptibility_laplace(-S.I*w,m))
    total=S.simplify(w*S.im(phasor_material_epsilon(w,m)))
    relaxation=S.simplify(m.gamma*w*w/m.alpha*chi*S.conjugate(chi))
    return dict(total=total,ohmic=m.sigma,relaxation=relaxation,
                residual=S.simplify(total-m.sigma-relaxation))


def coupled_maxwell_generator(omega,kx=0,ky=0,material=None):
    m=(material or LorentzMaterial()).validated()
    eps=phasor_material_epsilon(omega,m)
    return oblique_generator(S.sympify(omega),S.sympify(kx),S.sympify(ky),
                             m.mu,eps*S.eye(3))


def spectral_flux_loss(omega,material=None):
    m=(material or LorentzMaterial()).validated()
    M=coupled_maxwell_generator(omega,0,0,m)
    return S.simplify(M.conjugate().T*F+F*M)
