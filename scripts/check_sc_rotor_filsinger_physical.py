#!/usr/bin/env python3
"""Physically dimensioned rotor/nonlinear-response tests; no invented observations.

Classical mechanics owner: angular speed (rad/s), rotational stress (Pa),
kinetic energy (J), drive power (W). Damped ADE owner: SmithFilsinger
LorentzADE Maxwell source. Anomalous gravity coefficient is NOT derived.

Original regime authorities:
Hathaway/Cleveland/Bao Physica C 385 (2003) 488-500
Graham et al Physica C 468 (2008)
Tajmar et al arXiv:0707.3806

The quartic response illustrates nonlinear material/source response *possible*
within the old null bound; it is equally possible for ordinary artefacts.
"""
import sympy as s

def check():
    rpm=s.symbols('rpm',real=True)
    omega=2*s.pi*rpm/60
    ratio=s.factor(omega.subs(rpm,2000)/omega.subs(rpm,550))
    assert ratio==s.Rational(40,11)
    assert ratio**2==s.Rational(1600,121)
    rho,R,I=s.symbols('rho R I',positive=True)
    stress=rho*(R*omega)**2  # characteristic Pa (geometry coefficient separate)
    assert s.simplify(stress/(rho*R**2*omega**2)-1)==0
    energy=I*omega**2/s.Integer(2) # J if I kg m^2, omega s^-1
    assert s.simplify(s.diff(energy,rpm)-I*omega*s.diff(omega,rpm))==0
    # The readout is an ADE low-frequency ENVELOPE response:
    # do not equate 4-5 MHz RF carrier with 10-30Hz rotor frequency.
    w,w0,gamma,kappa=s.symbols('w w0 gamma kappa',positive=True)
    chi=kappa/(w0**2-w**2+s.I*2*gamma*w)
    assert s.simplify(chi*s.conjugate(chi)-
       kappa**2/((w0**2-w**2)**2+4*gamma**2*w**2))==0
    # Graham alternative response: acceleration impulse relaxes away on a
    # constant-speed plateau; it is not Graham's tested velocity-proportional law.
    time,tresponse,a0=s.symbols('time tresponse a0',positive=True)
    y=a0*s.exp(-time/tresponse)
    assert s.simplify(tresponse*s.diff(y,time)+y)==0
    assert s.limit(y,time,s.oo)==0
    # Explicit even/odd rotor parity. Data are required to choose coefficients.
    Codd,Ceven=s.symbols('Codd Ceven',real=True)
    response=Codd*omega+Ceven*omega**2
    assert s.simplify((response-response.subs(rpm,-rpm))/2-Codd*omega)==0
    assert s.simplify((response+response.subs(rpm,-rpm))/2-Ceven*omega**2)==0
    # A *candidate* superconducting material gate depends on measured
    # Tc and trapped flux, not an arbitrary 550rpm cutoff.
    Btrap,C,Tc,T=s.symbols('Btrap C Tc T',positive=True)
    Ps=s.Piecewise((0,T>=Tc),(1-(T/Tc)**2,True))
    candidate=C*Ps*Btrap*omega**4 # C bears needed dimensional transfer
    assert s.simplify(candidate.subs(Btrap,0))==0
    assert s.simplify(candidate.subs(T,2*Tc))==0
    assert s.simplify(candidate.subs(T,Tc/2)/candidate.subs(T,Tc/4)-s.Rational(4,5))==0
    # A 0.001% bound at 550rpm cannot produce 0.05% at 2000rpm
    # under fixed quadratic response; quartic reaches it without violating bound.
    null_limit=s.Rational(1,1000) # percent
    claim=s.Rational(5,100) # percent
    assert null_limit*ratio**2<claim
    assert null_limit*ratio**4>claim
    coefficient=claim/omega.subs(rpm,2000)**4
    assert s.simplify(coefficient*omega.subs(rpm,550)**4)<null_limit
    assert s.simplify(coefficient*omega.subs(rpm,2000)**4-claim)==0
    print('PASS exact SI-scale mechanics, ADE, rotation parity, Tc/flux controls')
    print('quadratic and quartic speed ratios:',ratio**2,ratio**4)
    print('CAUTION: synthetic constitutive power law, not observed gravity or raw replication')

if __name__=='__main__':check()
