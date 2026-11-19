"""Conditional reverse targets: closed-current phantom MCG and KK atomic-unit/BCS model.
No calibrated REBCO or measured remote human signal. SI except symbolic slopes.
"""
import numpy as np
import sympy as s
from scipy.integrate import solve_ivp
from scipy.optimize import brentq
from math import pi,sqrt,exp
# Dimensionless radion theta=phi/M4; electron, ion, fine structure slopes.
e,i,a=s.symbols('e i a',real=True)
Eh=e+2*a; a0=-e-a; K=Eh-2*a0; t=Eh
phonon=s.expand((K-i)/2)
gap=phonon # fixed dimensionless pairing, weak coupling; derivative log gap
assert s.simplify(gap-t-(e-i)/2)==0
xi,D=s.symbols('xi D',real=True)
O=s.factor(xi*D*(gap-t)); assert s.simplify(O-xi*D*(e-i)/2)==0
# geometric KK scalar mass slopes
fe,fi=s.symbols('f_e f_i',real=True)
diff=s.simplify(((e-i)/2).subs({e:-(1+2*fe)/s.sqrt(6),i:-(1+2*fi)/s.sqrt(6)}))
assert s.simplify(diff-(fi-fe)/s.sqrt(6))==0
print('KK atomic scaling slopes:', 'hopping',t,'phonon',phonon,'differential',diff)
# normalized scalar quantum mode; illustrative volume and frequency, not a cavity solution
G=6.67430e-11;c=299792458.;hb=1.054571817e-34;ev=1.602176634e-19
w=2*pi*3.5e6;V=1e-3;theta0=sqrt(4*pi*G*hb/(c*c*V*w)); T=27.5
Greq=pi/(2*T); print('scalar zero point theta',theta0,'required collective transition energy eV',hb*Greq/theta0/ev)
# finite-time sweep compared with resonant protocol at equal G, T, equal loss
# units are angular frequency, probability not energy for swept mode

def transfer(G,ratio,gamma=0):
    def rhs(u,z):
        d=ratio*G*(2*u-1);return -1j*T*np.array([d*z[0]/2+G*z[1],G*z[0]-d*z[1]/2])-gamma*T*z/2
    z=solve_ivp(rhs,(0,1),[1+0j,0j],rtol=1e-10,atol=1e-12).y[:,-1]
    assert abs(np.vdot(z,z).real-exp(-gamma*T))<1e-8
    return abs(z[1])**2
for g in (Greq,.3551372847):
    for r in (0,1,5,10): print('sweep',g,r,transfer(g,r),transfer(g,r,.001))
# closed-current axisymmetric phantom loop: far dipole and area optimization
mu0=1.25663706212e-6; B0=50e-12;r0=.1;R=1000.;B=B0*(r0/R)**3
N=1000;time=86400.;asd=1e-16;snr=5
# one-sided ASD, sinusoid peak amplitude, known phase, long time: rho=B sqrt(N*T)/asd
need=snr*asd/(B*sqrt(N*time));print('phantom B',B,'required independent amplitude improvement',need,'ASD target',asd/need)
Rloop,z,m=s.symbols('R z m',positive=True)
flux=Rloop**2/(Rloop**2+z**2)**s.Rational(3,2)
assert s.simplify(s.diff(flux,Rloop).subs(Rloop,s.sqrt(2)*z))==0
# projection check: whitened nuisance elimination, exactly dark when collinear
u=np.ones(4); v=np.array([1.,-1,1,-1]);P=np.eye(4)-np.outer(u,u)/(u@u)
assert np.allclose(P@u,0) and np.allclose(P@v,v)
print('PASS symbolic slopes, finite sweep norm, phantom geometry and nuisance projection')
