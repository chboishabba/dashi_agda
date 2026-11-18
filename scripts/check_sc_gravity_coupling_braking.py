#!/usr/bin/env python3
"""Conditional superconducting/gravitation coupling and NASA braking scope.
Original source: Li & Torr PRD43 (1991), PRB46 (1992); Kowitt PRB49 (1994);
Noever, Koczor, Robertson NASA NTRS 19990019627; Podkletnov 1997.
Mathematical model is newly constructed, NOT measured gravity, GL/GR solution
or a physical derivation of the nonstandard scalar coupling.
"""
import sympy as s

def check():
    x,phi,xd,pd,T,td,u,ud,lam,ld=s.symbols(
       'x phi xd pd T td u ud lam ld',real=True)
    a,b,Tc,Gamma,m0=s.symbols('a b Tc Gamma m0',positive=True)
    F=a*(T-Tc)*x**2/2+b*x**4/4-u*x+(m0*m0+lam*x*x)*phi*phi/2
    dF=s.diff(F,x)*xd+s.diff(F,phi)*pd+s.diff(F,T)*td+s.diff(F,u)*ud+s.diff(F,lam)*ld
    assert s.expand(dF-s.diff(F,x)*xd-s.diff(F,phi)*pd-
                   s.diff(F,T)*td-s.diff(F,u)*ud-s.diff(F,lam)*ld)==0
    assert s.diff(F,u)==-x
    assert s.diff(F,lam)==x*x*phi*phi/2
    assert s.simplify(s.diff(F,phi,phi).subs(x,0)-m0**2)==0
    q,d=s.symbols('q d',positive=True)
    transfer=s.Matrix([[s.cosh(q*d),s.sinh(q*d)/q],
                       [q*s.sinh(q*d),s.cosh(q*d)]])
    assert s.simplify(transfer.det()-1)==0
    # Exponential is a single-decaying-branch asymptotic; complete static
    # boundary matching must use transfer and external source geometry.
    eps=s.Rational(2,100)
    required=-s.log(1-eps)
    assert s.simplify(s.exp(-required)-(1-eps))==0
    Or,Of,ar,af,p=s.symbols('Or Of ar af p',real=True)
    slip=Of-p*Or
    slipdot=af-p*ar
    assert s.diff(slip,Or)==-p
    assert slipdot.subs({af:0,ar:1})==-p
    assert slipdot.subs({af:1,ar:0})==1
    assert slipdot.subs({af:0,ar:0})==0
    ad25=s.Rational(1500,25)*2*s.pi/60
    ad30=s.Rational(1500,30)*2*s.pi/60
    af25=s.Rational(12000,25)*2*s.pi/60
    af30=s.Rational(12000,30)*2*s.pi/60
    assert s.simplify(af25/ad25)==8
    assert s.simplify(af30/ad30)==8
    g=6.67430e-11*.8/(.1**2*9.80665)
    assert 5.4e-10<g<5.5e-10
    print('PASS scalar Landau coupling work, exact 1D mode-transfer determinant')
    print('2% *hypothetical full-field* decaying branch q [m^-1] at d=1cm:',
          float(required/s.Rational(1,100)))
    print('Ordinary 0.8kg rotor Newtonian acceleration / Earth g, r=10cm:',g)
    print('Additional local-source acceleration factor to 2%:',.02/g)
    print('Reported disk-braking endpoint-mean decel:',float(ad30),float(ad25),'rad/s²')
    print('HYPOTHETICAL 12000rpm stator-field-to-zero over 25-30s:',
          float(af30),float(af25),'rad/s²; no source claim this was run')
    print('Three mechanisms: rotor acceleration, stator acceleration, slip acceleration')
    print('OPEN original NASA ramps, material x(t), scalar universal coupling, GR/Maxwell weld')
if __name__=='__main__':check()
