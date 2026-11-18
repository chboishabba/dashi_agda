#!/usr/bin/env python3
"""Conditional nonlinear superconducting receiver, NOT a gravity detection.

Donors: SmithFilsinger Lorentz-ADE power balance, LiTorr source/constitutive
split. Historical scopes: Hathaway/Cleveland/Bao 2003 rotating disk RF weight;
Graham et al 2008 rotating lead + ring laser; Tajmar 2007/08 transition mismatch.
All response fixtures below are invented hypotheses, not fitted observations.
"""
import sympy as s

def main():
    w,gamma,h=s.symbols('w gamma h',positive=True)
    # One quadrature of an ideal below-threshold degenerate parametric pump:
    k=h*w/s.Integer(4)
    gain=gamma/(gamma-k)
    assert s.simplify(gain.subs(h,0)-1)==0
    assert s.simplify(gain.subs(h,2*gamma/w)-2)==0
    assert s.simplify(s.solve(s.Eq(k,gamma),h)[0]-4*gamma/w)==0
    Nin,Nread,sig=s.symbols('Nin Nread sig',positive=True)
    info=s.factor((gain*sig)**2/(gain**2*Nin+Nread))
    assert s.simplify(s.limit(info,h,0)-sig**2/(Nin+Nread))==0
    assert s.simplify(s.limit(info,h,4*gamma/w,dir='-')-sig**2/Nin)==0
    assert s.simplify(sig**2/Nin-info-
        sig**2*Nread/(Nin*(Nin*gain**2+Nread)))==0
    # Deliberately CONDITIONAL phenomenological anomalous channel:
    alpha,drive,coherence,phase=s.symbols('alpha drive coherence phase',real=True)
    detuning,linewidth=s.symbols('detuning linewidth',real=True,nonzero=True)
    eta=1+alpha*coherence*drive**2/(1+drive**2)*(
        linewidth**2/(linewidth**2+detuning**2))*s.cos(phase)
    for setting in ({drive:0},{coherence:0},{phase:s.pi/2}):
        assert s.simplify(eta.subs(setting)-1)==0
    assert s.simplify(eta.subs(phase,s.pi)-1+
        alpha*coherence*drive**2/(1+drive**2)*(
        linewidth**2/(linewidth**2+detuning**2)))==0
    G=s.symbols('G',positive=True)
    assert s.simplify((G*sig)/G-sig)==0
    # Illustrative reverse-capability input, NOT a biological upper bound.
    A0=s.Rational(50) # pT at 0.1 metre
    r0=s.Rational(1,10)
    r=s.Integer(1000)
    N=s.Integer(1000)
    T=s.Integer(86400)
    rho=s.Integer(5)
    asd=s.Rational(1,10000) # pT/sqrtHz = 0.1 fT/sqrtHz
    A=A0*(r0/r)**3
    required=s.simplify(rho*asd/(A*s.sqrt(N*T)))
    assert required>1000
    print('1km one-day required additional amplitude sensitivity factor',
          s.N(required,11))
    print('corresponding information factor',s.N(required**2,11))
    print('PASS exact pump/no-pump, phase, gain/noise saturation controls')
    print('NO physical nonzero alpha fitted; NO reproduction of original raw experimental data.')

if __name__=='__main__':main()
