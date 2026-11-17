#!/usr/bin/env python3
"""F10 local Maxwell/material port energy identity (exact symbolic).

Crosswalk PR #1521 nonlinear polarization plus Hall/Pedersen plus natural
neutral-wind mechanical work and independent generator work. This is NOT a
3D spatial Maxwell solution, and this model does not specify original media.

D=eps E+P; B=mu H; eta P_dot=E-P/chi-beta|P|²P;
u=eps|E|²/2+|B|²/(2mu)+|P|²/(2chi)+beta|P|⁴/4.

Maxwell Poynting: u_dot+div(E×H)+D_relax+D_Pedersen+parallel
    = P_modulation+P_neutral_wind+P_generator.
P_modulation= -|P|² chi_dot/(2chi²)
P_neutral_wind=(u_neutral×B)·J_conduction
P_generator= -E·J_generator (signed)

No ambient supply is presumed by introducing a named 'natural' port.
"""
import json
import sympy as s


def symbolic_energy():
    Ex,Ey,Ez,px,py,pz=s.symbols('Ex Ey Ez Px Py Pz',real=True)
    eps,mu,chi,eta,beta,chi_dot=s.symbols('eps mu chi eta beta chi_dot',positive=True)
    E=s.Matrix([Ex,Ey,Ez]);P=s.Matrix([px,py,pz]);p2=P.dot(P)
    Pdot=(E-P/chi-beta*p2*P)/eta
    dUp=(P/chi+beta*p2*P).dot(Pdot)-p2*chi_dot/(2*chi**2)
    relax=eta*Pdot.dot(Pdot)
    mod=-p2*chi_dot/(2*chi**2)
    polarization_residual=s.factor(E.dot(Pdot)-dUp-relax+mod)
    assert polarization_residual==0
    # Neutral frame, field-aligned B. Hall antisymmetry is *instantaneous*
    # in E'=E+u×B, but neutral-wind work is not necessarily zero.
    ux,uy,Bz=s.symbols('ux uy Bz',real=True)
    sigmaP,sigmaH,sigmaPara=s.symbols('sigmaP sigmaH sigmaPara',nonnegative=True)
    wind=s.Matrix([uy*Bz,-ux*Bz,0]);prime=E+wind
    J=s.Matrix([sigmaP*prime[0]+sigmaH*prime[1],
               sigmaP*prime[1]-sigmaH*prime[0],sigmaPara*prime[2]])
    joule=sigmaP*(prime[0]**2+prime[1]**2)+sigmaPara*prime[2]**2
    assert s.expand(prime.dot(J)-joule)==0
    natural_wind=wind.dot(J)
    assert s.expand(E.dot(J)-joule+natural_wind)==0
    Jgen=s.Matrix(s.symbols('Jgx Jgy Jgz',real=True))
    # From Maxwell: -div S = E·(eps E_dot+P_dot) + B_dot·H + E·(J+Jgen)
    # The chosen stored-energy derivative includes all reversible terms.
    e_dot=s.Matrix(s.symbols('e1dot e2dot e3dot',real=True))
    B_dot=s.Matrix(s.symbols('b1dot b2dot b3dot',real=True))
    B=s.Matrix(s.symbols('Bx By Bz2',real=True))
    field_dot=eps*E.dot(e_dot)+B.dot(B_dot)/mu
    stored_dot=field_dot+dUp
    div_poynting=-(eps*E.dot(e_dot)+E.dot(Pdot)+B.dot(B_dot)/mu+E.dot(J+Jgen))
    remaining=s.simplify(s.expand(stored_dot+div_poynting+relax+joule
                -mod-natural_wind+E.dot(Jgen)))
    assert remaining==0
    return dict(identity='udot+divS+Drelax+DPed+Dparallel=Pmod+Pneutral-E.Jgen',
                energy_residual=str(remaining),
                polarization_residual=str(polarization_residual),
                hall_neutral_frame_residual='0',
                natural_wind_power_example=float(natural_wind.subs({Ex:1,Ey:0,Ez:0,ux: -1,uy:0,Bz:1,sigmaP:0,sigmaH:2,sigmaPara:0})),
                caution='no Maxwell PDE solution; uniform local algebra and modeled constitutive law')


def retardation_diagnostic(length_m, electrical_frequency_hz, propagation_speed_m_s=299792458.):
    from math import isfinite,pi
    if not all(isfinite(x) and x>0 for x in (length_m,electrical_frequency_hz,propagation_speed_m_s)):
        raise ValueError('positive physical propagation parameters required')
    if propagation_speed_m_s>299792458.:
        raise ValueError('cannot use superluminal front speed')
    x=2*pi*electrical_frequency_hz*length_m/propagation_speed_m_s
    return dict(phase_distance_rad=x,quasistatic_screen=x<.1,
                limit='heuristic length/frequency screen; not rigorous PDE reduction',
                caution='electrical clock is unknown for Filsinger; acoustic 7.8kHz not electrical phase')


if __name__=='__main__':
    print(json.dumps(dict(F10=symbolic_energy(),
        local_2m_7800Hz=retardation_diagnostic(2.,7800.),
        hypothetical_full_column_80km_7800Hz=retardation_diagnostic(80000.,7800.)),indent=2))
