#!/usr/bin/env python3
"""Conditional coherent lattice/condensate braking: exact mechanics, flux and sources.

Provenance: London moment, rotating-superconductor TDGL/vortex literature;
Filsinger signed source/pump ledger and DASHI original KK reduced-action.
Original user hypothesis: coherent charged matter with braking-induced phase lag.
NOT full charged gauge-covariant TDGL, KK field equations or measured gravity.
"""
import sympy as s

def check():
    Il, Is, Om_l, Om_s, psi, K, eta, Ds = s.symbols(
        'I_l I_s Omega_l Omega_s psi K eta D_s', positive=True, real=True)
    Text, Trf = s.symbols('T_ext T_rf', real=True)
    delta = Om_l-Om_s
    Tcouple=K*psi+eta*delta
    Omldot=(Text-Tcouple)/Il
    Omsdot=(Trf+Tcouple-Ds*Om_s)/Is
    psidot=delta
    E=(Il*Om_l**2+Is*Om_s**2+K*psi**2)/2
    Edot=s.expand(s.diff(E,Om_l)*Omldot+s.diff(E,Om_s)*Omsdot+s.diff(E,psi)*psidot)
    assert s.simplify(Edot-Text*Om_l-Trf*Om_s+eta*delta**2+Ds*Om_s**2)==0
    t,tau,a,Om0,Tb=s.symbols('t tau a Omega_0 T_b',positive=True,real=True)
    Oml=Om0-a*t
    Oms=Om0-a*t+a*tau*(1-s.exp(-t/tau))
    assert s.simplify(s.diff(Oms,t)-(Oml-Oms)/tau)==0
    lag=s.simplify(Oms-Oml)
    assert lag.subs(t,0)==0
    assert s.simplify(s.limit(lag,t,s.oo)-a*tau)==0  # formal prolonged ramp
    tf=s.symbols('t_f',nonnegative=True)
    final_lag=lag.subs(t,Tb)*s.exp(-tf/tau)
    assert s.simplify(s.diff(final_lag,tf)+final_lag/tau)==0
    m,q,mu0,V=s.symbols('m q mu0 V',nonzero=True,real=True)
    Bl=-2*m*Oml/q
    Bs=-2*m*Oms/q
    dB=s.simplify(Bs-Bl)
    assert s.simplify(dB+2*m*lag/q)==0
    Du=s.simplify((Bs**2-Bl**2)/(2*mu0))
    assert s.simplify(Du-(Bs+Bl)*dB/(2*mu0))==0
    assert s.simplify((Du*V)-(Bs**2-Bl**2)*V/(2*mu0))==0
    varphi,M,F2=s.symbols('varphi M F2',real=True,positive=True)
    Z=s.exp(s.sqrt(6)*varphi/M)
    source=s.diff(-Z*F2/4,varphi)
    assert s.simplify(source.subs(varphi,0)+s.sqrt(6)*F2/(4*M))==0
    w,c,mp,hbar,k=s.symbols('w c m_phi hbar k',positive=True)
    Dmode=-(w/c)**2+k**2+(mp*c/hbar)**2
    assert s.simplify(Dmode.subs(w,mp*c**2/hbar)-k**2)==0
    from math import pi,exp
    a_val=(5000-3500)*2*pi/(60*27.5)
    for tau_val in (0.01,0.1,1,10):
        lagval=a_val*tau_val*(1-exp(-27.5/tau_val))
        print(f'lag at braking end for tau={tau_val:g}s: {lagval:.9g} rad/s')
    coeff=2*9.1093837139e-31/1.602176634e-19
    print('London field difference for tau=1s at end, tesla:',coeff*a_val*(1-exp(-27.5)))
    print('PASS exact two-inertia power balance, ramp/hold, London flux, KK source and dispersion')
    print('OPEN material tau, local vortex/TDGL state, full exterior BVP, quantum source')

if __name__=='__main__':check()
