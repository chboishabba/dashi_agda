#!/usr/bin/env python3
"""Filsinger nonlinear capacitor pump, cardiac sidebands and SQUID input-noise.

Reuses exact q=C0 V+alpha V^3 and U=C0 V^2/2+3alpha V^4/4 from
Docs/research/SmithFilsingerDispersiveSourceResponseMaxCut20261115.md,
and the signed source/modulation work boundary in SmithFilsinger materials.
Capacitor is a conditional nonlinear mixer, not measured SQUID coupling.
"""
import sympy as s

def check():
    C0,alpha,Vb,Vp,vs,Omega,omega,t=s.symbols(
       "C0 alpha Vb Vp vs Omega omega t",real=True)
    V,P=s.symbols("V P",real=True)
    Q=C0*V+alpha*V**3
    U=C0*V**2/2+3*alpha*V**4/4
    assert s.expand(s.diff(U,V)-V*s.diff(Q,V))==0
    differential=s.expand(s.diff(Q,V).subs(V,Vb+Vp*P))
    cbar=C0+3*alpha*Vb**2+s.Rational(3,2)*alpha*Vp**2
    c1=6*alpha*Vb*Vp
    c2=s.Rational(3,2)*alpha*Vp**2
    assert s.expand(differential-cbar-c1*P-c2*(2*P**2-1))==0
    assert s.simplify(c1*vs/2-3*alpha*Vb*Vp*vs)==0
    assert c1.subs(Vb,0)==0
    assert s.simplify(c2.subs(Vb,0)*vs/2-3*alpha*Vp**2*vs/4)==0
    # sidebands q(Omega +/- omega): first carrier; q(2Omega +/- omega)
    # at zero bias. Output current requires frequency differentiation.
    Cap,Vx,Cdot,Vdot=s.symbols("Cap Vx Cdot Vdot",real=True)
    work=Vx*(Cap*Vdot+Cdot*Vx)
    dU=Cap*Vx*Vdot+Cdot*Vx**2/2
    assert s.expand(work-dU-Cdot*Vx**2/2)==0
    # Magnetic field B -> pickup -> SQUID flux -> nonlinear frequency converter
    M,Ap,Lp,Li,B=s.symbols("M Ap Lp Li B",positive=True)
    chiB=M*Ap/(Lp+Li)
    assert s.diff(chiB*B,B)==chiB
    R,Sin,Sflux,Spump,Sdown=s.symbols(
        "R Sin Sflux Spump Sdown",positive=True)
    Sout=R**2*(chiB**2*Sin+Sflux+Spump)+Sdown
    equivalent=s.factor(Sout/(R*chiB)**2)
    expected=Sin+(Sflux+Spump)/chiB**2+Sdown/(R**2*chiB**2)
    assert s.simplify(equivalent-expected)==0
    assert s.simplify(s.limit(equivalent,R,s.oo)-Sin-(Sflux+Spump)/chiB**2)==0
    frac=s.symbols("frac",positive=True)
    assert s.simplify(s.sqrt(1/frac).subs(frac,s.Rational(1,1076**2))-1076)==0
    print("PASS Filsinger capacitor, pumped sidebands, modulation work, field-to-flux and noise")
    print("Omega sideband charge amplitude:",c1*vs/2)
    print("2Omega sideband charge amplitude:",c2*vs/2)
    print("Input-equivalent noise:",expected)
    print("OPEN measured nonlinear alpha, pump coupling, converted cardiac-band noise")

if __name__=="__main__":check()
