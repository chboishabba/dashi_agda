#!/usr/bin/env python3
"""Exact paper-table rotor discriminator, not reproduction of experiment.

E E Podkletnov (1997), arXiv:cond-mat/9701074, section 6:
6 original attributed 2MHz steady rows + 3.2–3.8MHz braking report.
G Hathaway, B Cleveland, Y Bao, Physica C 385 (2003) 488–500:
~0.5 MPa at ~1300rpm for their specific fragile disk.
Derived fit is conditional, no gravity observation or coefficient inferred.
"""
from fractions import Fraction as F
import math
import sympy as s

def check():
    rpm=(4000,4200,4400,4600,4800,5000)
    pct=tuple(F(k,100) for k in (17,19,20,21,22,23))
    n=len(rpm)
    xb=sum(map(F,rpm),F())/n
    yb=sum(pct,F())/n
    slope=sum((F(x)-xb)*(y-yb) for x,y in zip(rpm,pct))/sum((F(x)-xb)**2 for x in rpm)
    offset=yb-slope*xb
    assert slope==F(1,17500)
    assert offset==F(-113,2100)
    residual=sum((y-offset-slope*x)**2 for x,y in zip(rpm,pct))
    total=sum((y-yb)**2 for y in pct)
    assert 1-residual/total==F(48,49)
    extrapolate=lambda target:(F(target)-offset)/slope
    assert extrapolate(F(30,100))==F(18575,3)
    assert extrapolate(2)==F(107825,3)
    # These are not same-drive data: reported 2% is under braking,
    # temperature, height and RF conditions differ.
    delta=s.Rational(177,100)
    alpha25=1500*2*s.pi/(60*25)
    alpha30=1500*2*s.pi/(60*30)
    assert s.simplify(delta/alpha25-s.Rational(177,200)/s.pi)==0
    assert s.simplify(delta/alpha30-s.Rational(531,500)/s.pi)==0
    # Levitation changes contact losses but cannot erase hoop stress.
    omega,omegadot,I=s.symbols("omega omegadot I",real=True)
    E=I*omega**2/2
    Pbrake=-I*omega*omegadot
    assert s.simplify(Pbrake+s.diff(E,omega)*omegadot)==0
    rate=s.symbols("rate",positive=True)
    stress=s.Rational(1,2)*(rate/1300)**2
    assert s.simplify(stress.subs(rate,5000)/stress.subs(rate,1300))==s.Rational(2500,169)
    # Baseline conventional gravity of kinetic energy as effective mass.
    # Ring approximation, not a full stress-energy/Einstein solution.
    Gn=6.67430e-11; c=299792458.; m=.8; R=.1375; z=.1
    w=5000*2*math.pi/60
    Erot=.5*m*R**2*w**2
    delta_g_over_g=Gn*Erot/(c*c*z*z*9.80665)
    assert 1e-24<delta_g_over_g<2e-23
    # Exact original Filsinger nonlinear capacitor storage work law.
    V,C,a=s.symbols("V C a",real=True)
    q=C*V+a*V**3
    U=C*V**2/2+3*a*V**4/4
    assert s.expand(s.diff(U,V)-V*s.diff(q,V))==0
    print("PASS exact original six-row fit, braking port, stress and capacitor energy")
    print("source steady 2MHz fit pct/rpm",slope,"offset pct",offset,"R2",1-residual/total)
    print("fictitious SAME-DRIVE extrapolations rpm for 0.3%, 2%:",
         extrapolate(F(30,100)),extrapolate(2))
    print("reported braking alpha magnitude rad/s², 25–30 s:",alpha25,alpha30)
    print("if 1.77 percentage-point difference treated as transient, apparent coefficient:",
         s.simplify(delta/alpha25),s.simplify(delta/alpha30),
         "percentage points/(rad/s²); NO causal interpretation")
    print("thin-ring ordinary rotational energy joule",Erot,
          "conventional delta-g/g scale",delta_g_over_g)
    print("Open: measured angular acceleration, RF power, flux state, inertial probe,")
    print("      transient causal coupling, phase-matched original experiments")
if __name__=="__main__":check()
