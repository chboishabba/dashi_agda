#!/usr/bin/env python3
"""Driven superconducting vortex washboard radiation and signed source work.

Prior physics: PRL 97 197002 (2006) vortex edge radiation;
PRB 61 12389 (2000) vortex transition radiation. Original theorists own
radiative mechanism. Filsinger source/port ledger reused. All fixture
velocities are examples, not measured rotor/vortex motion or gravity effects.
"""
import math
import sympy as s
PHI0=2.067833848e-15
def main():
    x,eta,U0,a,J,phi0=s.symbols('x eta U0 a J phi0',positive=True,real=True)
    U=U0*(1-s.cos(2*s.pi*x/a))
    grad=s.diff(U,x)
    xdot=(phi0*J-grad)/eta
    assert s.simplify(grad*xdot+eta*xdot**2-phi0*J*xdot)==0
    # Periodic pinning force, vortex-lattice approximation spacing sqrt(Phi0/B)
    vel,B=s.symbols('vel B',positive=True)
    spacing=s.sqrt(phi0/B)
    f=s.simplify(vel/spacing)
    assert s.simplify(f-vel*s.sqrt(B/phi0))==0
    sep=math.sqrt(PHI0)
    f10=10/sep
    assert 2e8<f10<3e8
    # This is vortex drift velocity, NOT mechanical rim speed.
    amp,eps,Omega,w,t=s.symbols('amp eps Omega w t',real=True)
    mod=(amp+eps*s.cos(Omega*t))*s.cos(w*t)
    sides=amp*s.cos(w*t)+eps*(s.cos((w+Omega)*t)+s.cos((w-Omega)*t))/2
    assert s.trigsimp(mod-sides)==0
    # Fourier projected KK scalar mode, with field-source work explicitly paid
    Q,P,wn,S=s.symbols('Q P wn S',real=True)
    E=(P**2+wn**2*Q**2)/2
    Qdot=P
    Pdot=S-wn**2*Q
    assert s.simplify(s.diff(E,Q)*Qdot+s.diff(E,P)*Pdot-S*Qdot)==0
    print('PASS exact vortex pinning-work, washboard and parametric sidebands')
    print('At B=1 T ideal intervortex scale m:',sep)
    print('At assumed vortex velocity=10 m/s radiation fundamental Hz:',f10)
    print('Corresponding photon energy J:',6.62607015e-34*f10)
    print('NOT measured radiation power; no original source-to-vortex-speed mapping')
    print('OPEN REBCO Jc/viscosity/pinning, retarded Maxwell radiation and KK exterior')

if __name__=='__main__':main()
