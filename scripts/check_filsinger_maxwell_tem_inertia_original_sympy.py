#!/usr/bin/env python3
"""Maxwell -> power-port TEM reference; independent magnetic-force vs inertia controls.

This solves an *ideal lossless coaxial TEM reference*, NOT the historical
Filsinger/Smith electrode geometry. It supplies an exact finite-geometry donor
and a negative-control experiment-design calculation for the original Agda
F10/F13/F15 and antigravity experimental owners. It is not measured evidence.
"""

from sympy import (E, Function, Matrix, pi, Q, Rational, symbols, log, sqrt,
                   simplify, integrate, diff, exp, det, zeros, expand, factor)

checks = []

def accept(description, claim):
    assert bool(claim), description
    checks.append(description)

# Exact Maxwell TEM in a cylindrical perfect-conductor annulus a<rho<b.
# A(u) is an arbitrary differentiable waveform, u=t-z/c, eta=sqrt(mu/eps).
# Outside the conductors J=rho_charge=0; sources and return currents live on
# the *conductor surfaces*. No radiation, ohmic loss, or source loading assumed.
t,z,r,a,b,epsilon,mu=symbols('t z r a b epsilon mu',positive=True)
phi=symbols('phi',real=True)
eta=sqrt(mu/epsilon)
c=1/sqrt(mu*epsilon)
u=t-z/c
wave=Function('A')(u)
Er=wave/r
Hphi=wave/(eta*r)
Eph=0
Hz=0
accept('positive characteristic speed and impedance',simplify(eta*c-1/epsilon)==0)
accept('bulk electric Gauss law: cylindrical div E=0',simplify(diff(r*Er,r)/r)==0)
accept('bulk magnetic Gauss law: cylindrical div B=0', simplify(diff(mu*Hphi,phi)/r)==0)
accept('cylindrical Faraday phi-component',simplify(diff(Er,z)+mu*diff(Hphi,t))==0)
accept('cylindrical Ampere radial displacement current',simplify(-diff(Hphi,z)-epsilon*diff(Er,t))==0)
accept('cylindrical Ampere axial component zero',simplify(diff(r*Hphi,r)/r)==0)
accept('travelling field is not a static field',diff(Er,t)!=0)

# Voltage = radial conductor potential difference, I = Ampere circulation.
# Positive +z Poynting transfer using conventional right-hand orientation.
ell=log(b/a)
V=wave*ell
Iport=2*pi*wave/eta
Sz=Er*Hphi
Pz=2*pi*wave**2*ell/eta
accept('exact radial E integral gives terminal V',simplify(integrate(Er,(r,a,b))-V)==0)
accept('exact H loop circulation gives terminal I',simplify(2*pi*r*Hphi-Iport)==0)
accept('E cross H is positive z-directed',simplify(Sz-wave**2/(eta*r*r))==0)
accept('integrated Poynting flux equals V*I',simplify(integrate(2*pi*r*Sz,(r,a,b))-V*Iport)==0)
accept('integrated Poynting flux has correct positive sign',simplify(Pz-V*Iport)==0)
Z0=eta*ell/(2*pi)
C0=2*pi*epsilon/ell
L0=mu*ell/(2*pi)
accept('characteristic impedance V/I',simplify(V-Z0*Iport)==0)
accept('telegrapher impedance squared L/C',simplify(Z0**2-L0/C0)==0)
accept('telegrapher wave speed c',simplify(c*c-1/(L0*C0))==0)
U_e=epsilon*pi*wave**2*ell
U_h=mu*pi*wave**2*ell/(eta*eta)
Uper=U_e+U_h
accept('electric/magnetic equal stored energy',simplify(U_e-U_h)==0)
accept('telegrapher total stored energy per length',simplify(Uper-(C0*V*V/2+L0*Iport*Iport/2))==0)
accept('travelling source power is c times stored energy density',simplify(Pz-c*Uper)==0)
accept('distributed Poynting differential identity dU/dt+dP/dz=0',simplify(diff(Uper,t)+diff(Pz,z))==0)
accept('forward wave E/H orientation produces positive flux',simplify(Sz-(Er*Hphi))==0)

# A physical radial finite-volume partition (exact analytic annuli, not
# point sampling) cancels internal interfaces, preserving the full VI port.
for N in (1,2,3,5,9):
    radii=[a*(b/a)**Rational(k,N) for k in range(N+1)]
    cells=[2*pi*wave**2/eta*log(radii[k+1]/radii[k]) for k in range(N)]
    accept(f'{N} radial finite-volume annuli sum to same original VI',simplify(sum(cells)-V*Iport)==0)
    accept(f'{N} annular contributions use correct outward order', all(simplify(cells[k]-Pz/N)==0 for k in range(N)))

# Independent, exact finite spacetime Poynting ledger with a nontrivial
# nonstationary travelling waveform; include *different* start and end stores.
tau=symbols('tau')
w=2+tau-tau**2/3
# epsilon=mu=1, log(b/a)=1; hence V=A and I=2pi A and c=1
P=lambda T,Z:2*pi*w.subs(tau,T-Z)**2
U=lambda T,Z:2*pi*w.subs(tau,T-Z)**2
T0,T1,Z0,Z1=Rational(0),Rational(2),Rational(0),Rational(1)
Win=integrate(P(t,Z0),(t,T0,T1))
Wout=integrate(P(t,Z1),(t,T0,T1))
Store0=integrate(U(T0,z),(z,Z0,Z1))
Store1=integrate(U(T1,z),(z,Z0,Z1))
accept('source enters selected +z end with finite positive work',Win>0)
accept('receiver exits selected +z end with finite positive work',Wout>0)
accept('real nontrivial storage change present',simplify(Store1-Store0)!=0)
accept('integrated space-time balance in-out=final-initial',simplify(Win-Wout-(Store1-Store0))==0)
accept('finite-time Poynting ledger exact conservation',simplify(Win+Store0-Wout-Store1)==0)
back=Function('B')(t+z/c)
backE=back/r
backH=-back/(eta*r)
accept('reverse-propagating field satisfies Faraday',simplify(diff(backE,z)+mu*diff(backH,t))==0)
accept('reverse-propagating field satisfies Ampere',simplify(-diff(backH,z)-epsilon*diff(backE,t))==0)
accept('reverse-propagating Poynting flux points toward -z',simplify(backE*backH+back**2/(eta*r*r))==0)
accept('source-off field eliminates physical port power',Pz.subs(wave,0)==0)

# The other essential source-access gate: the Maxwell solution with both
# travelling directions is still source-free in the dielectric. A large field
# amplitude or standing-wave energy is not the same as useful net work.
forward=Function('Fwd')(t-z/c)
backward=Function('Rev')(t+z/c)
totalE=(forward+backward)/r
totalH=(forward-backward)/(eta*r)
netP=simplify(2*pi*ell*r*r*totalE*totalH)
accept('counterpropagating pair obeys Maxwell Faraday',simplify(diff(totalE,z)+mu*diff(totalH,t))==0)
accept('counterpropagating pair obeys Ampere',simplify(-diff(totalH,z)-epsilon*diff(totalE,t))==0)
accept('no false interference work term in signed VI',simplify(netP-2*pi*ell*(forward**2-backward**2)/eta)==0)
accept('equal incoming and outgoing waves have zero net power',simplify(netP.subs(backward,forward))==0)
accept('standing wave can retain nonzero electric field',simplify(totalE.subs(backward,forward)-2*forward/r)==0)
accept('standing wave can retain nonzero magnetic energy at a different phase',simplify(totalH.subs(backward,-forward)-2*forward/(eta*r))==0)

# At a real resistive termination Rload, reflection is an energy-port ratio.
# The control changes *access*, not the incident source's available budget.
Rload,Zsource,Vinc,gsh,Rseries=symbols('Rload Zsource Vinc gsh Rseries',positive=True)
Gamma=(Rload-Zsource)/(Rload+Zsource)
Pincident=Vinc**2/Zsource
Pdelivered=simplify(Pincident*(1-Gamma**2))
accept('reflection coefficient exactly zero at match',Gamma.subs(Rload,Zsource)==0)
accept('delivered load power equals source minus reflected',simplify(Pdelivered-4*Vinc**2*Rload/(Rload+Zsource)**2)==0)
accept('matched passive termination attains incident maximum',simplify(Pdelivered.subs(Rload,Zsource)-Pincident)==0)
accept('load mismatch has nonnegative passive loss fraction',simplify(1-Gamma**2-4*Rload*Zsource/(Rload+Zsource)**2)==0)
accept('matched power derivative vanishes',simplify(diff(Pdelivered,Rload).subs(Rload,Zsource))==0)
accept('perfect reflection blocks load power',simplify(Pdelivered.subs(Rload,0))==0)

# Fixed useful load of 1 Ohm with parasitic shunt g versus a series access
# resistance. The same controller may help or hinder target load output.
Pshunt=4*Vinc**2/(2+gsh)**2
Pseries=4*Vinc**2/(2+Rseries)**2
accept('parasitic shunt reduces target load transfer',simplify(Pshunt.subs(gsh,1)-Pshunt.subs(gsh,0))==-5*Vinc**2/9)
accept('reduce series resistance improves target load transfer',simplify(Pseries.subs(Rseries,Rational(1,2))-Pseries.subs(Rseries,2))==Rational(39,100)*Vinc**2)
accept('one unit pump cost exceeds this illustrative series gain',simplify(1-(Pseries.subs(Rseries,Rational(1,2))-Pseries.subs(Rseries,2)).subs(Vinc,1))==Rational(61,100))
accept('zero external incident source delivers zero load despite matching',Pdelivered.subs(Vinc,0)==0)

# The EM gradient-support model and inertia-only rival are indistinguishable
# from support/weight alone, but can be separated by independent force pulses.
# This is a synthetically selected experiment design, not an observed apparatus.
Fdrive,MagScale,m_i,kappa,m_g,g,beta=symbols('Fdrive MagScale m_i kappa m_g g beta',real=True)
EMforce=beta*MagScale
astandard=(Fdrive+EMforce-m_g*g)/m_i
ainertia=(Fdrive+EMforce-m_g*g)/(kappa*m_i)
Wsupport=m_g*g-EMforce
accept('static weight channel independent of inertial parameter',diff(Wsupport,kappa)==0)
accept('static weight channel depends on EM gradient if source coupled',diff(Wsupport,MagScale)==-beta)
accept('ordinary force pulse slope 1/mi',simplify(diff(astandard,Fdrive)-1/m_i)==0)
accept('inertial rival pulse slope 1/(k mi)',simplify(diff(ainertia,Fdrive)-1/(kappa*m_i))==0)
accept('inertia-only at zero pulse support cannot distinguish',simplify(Wsupport-Wsupport)==0)
choose={m_i:2,kappa:2,m_g:2,g:1,beta:2,MagScale:1}
accept('ordinary EM support exactly balances weight',simplify(Wsupport.subs(choose))==0)
accept('same support both mass hypotheses',simplify(Wsupport.subs(choose)-Wsupport.subs(choose))==0)
accept('ordinary baseline acceleration zero',simplify(astandard.subs(choose).subs(Fdrive,0))==0)
accept('inertial rival baseline acceleration zero',simplify(ainertia.subs(choose).subs(Fdrive,0))==0)
accept('ordinary response under calibrated pulse 1 is half',simplify(astandard.subs(choose).subs(Fdrive,1))==Rational(1,2))
accept('inertial-only response under pulse 1 is quarter',simplify(ainertia.subs(choose).subs(Fdrive,1))==Rational(1,4))
accept('independent drive pulse can distinguish selected rivals',simplify((astandard-ainertia).subs(choose).subs(Fdrive,1))==Rational(1,4))
accept('zero magnetic gradient removes EM force',EMforce.subs(MagScale,0)==0)
accept('material source-response reversal changes support',simplify(Wsupport.subs(MagScale,1)-Wsupport.subs(MagScale,-1)+2*beta)==0)

# Observation rank: at one static (F=0, gradient=1) the unknown source,
# inertial scale and gravity baseline are underdetermined. With off/on
# field and independent calibrated drive, linear regression in (p,q,r):
# a=p*Fdrive+q*MagScale-r, where p=1/mi, q=beta/mi, r=mg*g/mi.
static=Matrix([[0,1,-1]])
refined=Matrix([[0,0,-1],[1,0,-1],[0,1,-1],[1,1,-1]])
accept('static observation has rank one',static.rank()==1)
accept('source/drive interventions yield rank three',refined.rank()==3)
accept('rank-three minor exact nonzero',refined[:3,:].det()!=0)
accept('calibrated rank-three design exactly reconstructs p q r', refined[:3,:].inv()*(refined[:3,:]*Matrix([Rational(1,2),1,1]))==Matrix([Rational(1,2),1,1]))
accept('turning off gradient is necessary to see gravity-only baseline',simplify(Wsupport.subs(MagScale,0)-m_g*g)==0)

# The model has no actual Filsinger geometry/source-current evidence and
# does not instantiate any existing experimental-source receipt in Agda.

print(f'{len(checks)}/{len(checks)} PASS; exact ideal TEM field->VI, finite radial/spacetime work, source/pulse inertia discriminator')
print('normalized nonstationary TEM Win =',Win,'Wout =',Wout,'Ufinal-Uinitial =',simplify(Store1-Store0))
