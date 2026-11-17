"""Exact N=2 periodic 2D Fourier inverse of oblique Maxwell sheet Green.

A FOUR-MODE FINITE PERIODIC spectral Galerkin approximation, NOT the
continuous Fourier integral, a light-cone theorem, or real electrode VI.

The 2x2 transform has characters (-1)^(kx*x+ky*y); physical wavevectors
are supplied as integer 0/1 fixtures and are not deduced from a real grid
spacing. Matrix Green slices are reused, with no second Maxwell solver.
"""
import sympy as S
from smith_filsinger_oblique_maxwell_sympy import oblique_sheet_green
from smith_filsinger_radiation_green_sympy import flux_z,sheet_power_identity
MODES=((0,0),(0,1),(1,0),(1,1))


def sign_of(mode,position):
    return -1 if (mode[0]*position[0]+mode[1]*position[1])%2 else 1


def forward_periodic_2x2(source):
    if set(source)!=set(MODES):raise ValueError('source must have 2x2 grid')
    return {k:S.simplify(sum((sign_of(k,x)*source[x] for x in MODES),
                            S.zeros(2,1))/4) for k in MODES}


def inverse_periodic_2x2(modes):
    if set(modes)!=set(MODES):raise ValueError('four Fourier modes required')
    return {x:S.simplify(sum((sign_of(k,x)*modes[k] for k in MODES),
                            S.zeros(2,1))) for x in MODES}


def four_mode_green_field(T_by_mode,source,omega=2):
    freq=forward_periodic_2x2(source)
    responses={k:oblique_sheet_green(T_by_mode[k],omega,*k) for k in MODES}
    upper={k:S.simplify(responses[k]['upper_E']*freq[k]) for k in MODES}
    lower={k:S.simplify(responses[k]['lower_E']*freq[k]) for k in MODES}
    return dict(source_frequency=freq,response=responses,
                upper_modes=upper,lower_modes=lower,
                upper_grid=inverse_periodic_2x2(upper),
                lower_grid=inverse_periodic_2x2(lower))


def work_by_mode(result):
    by_mode={k:sheet_power_identity(result['response'][k],
                                   result['source_frequency'][k]) for k in MODES}
    total={name:S.simplify(sum((by_mode[k][name] for k in MODES),S.Integer(0)))
           for name in ('source','exterior','absorption','residual')}
    return by_mode,total


def grid_source_work(source,field):
    """Parseval identity: mean physical-sheet complex power = modal sum."""
    return S.simplify(sum((S.re((field[x].conjugate().T*source[x])[0])/2
                           for x in MODES),S.Integer(0))/4)
