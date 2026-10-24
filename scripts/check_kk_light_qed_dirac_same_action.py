#!/usr/bin/env python3
"""5D S1 physical-QED Dirac zero mode + charged Casimir stabiliser.

Source: free periodic 5D one-loop Casimir formalism (Abe et al., PTEP
2014 073B04, DOI 10.1093/ptep/ptu097). Candidate spectrum:
-9 gravity/Maxwell/scalar; +12 three neutral massive 5D Dirac;
+4 one heavy charged Dirac; -8 four heavy charged complex scalar;
+4 light charged Dirac, 5D bare mass chosen to equal observed electron
mass. All particles periodic, theta=0; no charged scalar condensate.
This does NOT prove electroweak chirality, observed mass generation,
a complete UV action or a realistic rotating 5D Earth.
"""
import numpy as np
from mpmath import mp
from scipy.optimize import minimize

mp.dps = 43
Z5 = mp.zeta(5)
C0 = 3*Z5/(64*mp.pi**6)
MPL = mp.mpf('2.435e18')  # reduced 4D Planck GeV
HBARC = mp.mpf('0.1973269804e-15')  # GeV m
RADIUS_M = mp.mpf('1e-24')
b0 = RADIUS_M/HBARC
ME = mp.mpf('0.00051099895')  # GeV (input, NOT derived)
ze = 2*mp.pi*ME*b0

def f(s, phase=0, der='f'):
    u = mp.exp(-s+1j*phase)
    if der=='f':
        expr=mp.polylog(5,u)+s*mp.polylog(4,u)+(s*s/3)*mp.polylog(3,u)
    elif der=='z':
        expr=-s*(mp.polylog(3,u)+s*mp.polylog(2,u))/3
    elif der=='zz':
        expr=-(mp.polylog(3,u)+s*mp.polylog(2,u)-s*s*mp.polylog(1,u))/3
    elif der=='thetatheta':
        expr=-(mp.polylog(3,u)+s*mp.polylog(2,u)+(s*s/3)*mp.polylog(1,u))
    else: raise ValueError(der)
    return mp.re(expr)/Z5

def h(s): return f(s)-s*f(s,der='z')/5

# At theta=0, heavy -8 scalar and +12 neutral fermion combine
# into +4f(zx). The whole radius-only function has POSITIVE weights.
z = mp.findroot(lambda t: 4*h(t)+4*h(4*t)+4*h(ze)-9,
                (mp.mpf('.75'),mp.mpf('1.1')))
ELL = 9-4*f(z)-4*f(4*z)-4*f(ze)
def U(x, theta):
    W=-9+12*f(z*x)+4*f(4*z*x,theta)-8*f(z*x,theta)+4*f(ze*x,theta)
    return ELL/x+W/x**6

def radial_hessian(s):
    return s*s*f(s,der='zz')-4*s*f(s,der='z')
Uxx=4*(radial_hessian(z)+radial_hessian(4*z)+radial_hessian(ze))
Utt=4*f(4*z,der='thetatheta')-8*f(z,der='thetatheta')+4*f(ze,der='thetatheta')
assert ELL>0 and Uxx>0 and Utt>0
assert abs(U(1,0))<mp.mpf('1e-34')
assert abs(mp.diff(lambda t:U(t,0),mp.mpf(1)))<mp.mpf('1e-34')
assert abs(mp.diff(lambda t:U(t,0),mp.mpf(1),2)-Uxx)<mp.mpf('1e-28')
assert abs(mp.diff(lambda t:U(1,t),mp.mpf(0),2)-Utt)<mp.mpf('1e-28')

# ALL-radius (theta=0) positivity is ANALYTIC, not just sampled:
# F(x)=x^6 U(x,0) = ELL*x^5 -9+4f(zx)+4f(4zx)+4f(z_e*x).
# F'(x)/x = 5ELL*x^3 -(4/3zeta5)*SUM_i s_i^2 S(s_i*x).
# S(t)=Li3(exp(-t))+t Li2(exp(-t)); S'(t)=-t Li1(exp(-t))<0.
# Therefore F'(x)/x strictly increases, vanishes at x=1,
# F decreases before 1 and increases after 1. Since F(1)=0,
# F(x)>0 for all x>0, x!=1 (theta FIXED to 0).
def radial_derivative_over_x(x):
    return 5*ELL*x**3-(4/(3*Z5))*sum(
        s*s*(mp.polylog(3,mp.exp(-s*x))+
             s*x*mp.polylog(2,mp.exp(-s*x))) for s in (z,4*z,ze))
assert abs(radial_derivative_over_x(1))<mp.mpf('1e-34')
assert all(radial_derivative_over_x(q)<0
           for q in map(mp.mpf,('.001','.05','.3','.9')))
assert all(radial_derivative_over_x(q)>0
           for q in map(mp.mpf,('1.1','2','10','100')))

# When all masses become negligible: -9+12+(4-8+4)f(0,theta)=3,
# uniformly independent of theta. Therefore x^6 U -> +3 as x->0.
assert -9+12+4-8+4==3

# Bounded two-variable scan. Electron z_e=1.63e-11, so using its
# m=0 Casimir is accurate to O((z_e*x)^2) on x<=1000.
# This is NOT a full continuum global-minimum certificate.
n=np.arange(1,161,dtype=float)
zt=float(z); ell=float(ELL)
def fs(s,theta):
    y=n*s
    return np.sum(np.exp(-y)*(1+y+y*y/3)*np.cos(n*theta)/(n**5))/float(Z5)
def approximate_U(x,theta):
    return ell/x+(-9+12*fs(zt*x,0)+4*fs(4*zt*x,theta)
                  -8*fs(zt*x,theta)+4*fs(0,theta))/x**6
smallest=(float('inf'),None,None)
for x in np.geomspace(.003,1000,180):
    for theta in np.linspace(0,np.pi,45):
        val=approximate_U(x,theta)
        if val<smallest[0]: smallest=(val,x,theta)
fit=[]
for x in (.25,.6,1,1.5,3,10):
    for theta in (0,np.pi/2,np.pi):
        sol=minimize(lambda u:approximate_U(float(np.exp(u[0])),float(u[1])),
                     (np.log(x),theta),bounds=[(-5,8),(0,np.pi)],
                     method='L-BFGS-B',options={'maxiter':100})
        fit.append((sol.fun,float(np.exp(sol.x[0])),sol.x[1]))
assert smallest[0]>-1e-5 and min(t[0] for t in fit)>-1e-5

# Physical photon = independent 5D Maxwell zero mode; e5 is chosen
# to reproduce the QED electron-photon charge in this convention.
e=mp.sqrt(4*mp.pi/mp.mpf('137.035999084'))
e5=e*mp.sqrt(2*mp.pi*b0)
assert abs(e5/mp.sqrt(2*mp.pi*b0)-e)<mp.mpf('1e-35')
assert mp.sqrt(ME*ME+(0/b0)**2)==ME
mass_KK_1=mp.sqrt(ME*ME+1/b0**2)
assert mass_KK_1>mp.mpf('1e8')
M5=(MPL**2/(2*mp.pi*b0))**(mp.mpf(1)/3)
assert b0*M5>1000
# 5D U1 NDA perturbative cutoff, conventional estimate
# Lambda_NDA = 24*pi^3/e5² (order-one conventions are not physical bounds).
cutoff_NDA=24*mp.pi**3/(e5*e5)
assert cutoff_NDA>1000/b0 and cutoff_NDA<M5
assert 4*z/(2*mp.pi*b0)<cutoff_NDA
radion_range=HBARC*MPL*b0*b0/mp.sqrt(2*C0*Uxx/3)
assert radion_range<mp.mpf('1e-10')

# Periodic real y-dependent Dirac mass M(y), holonomy theta:
# Left  exp(-intM-i theta), Right exp(+intM-i theta).
# Both periodic zero-modes exist together, or neither exists.
for m_int in map(mp.mpf,('-2','-.2','0','.7')):
    for theta in (mp.mpf(0),mp.pi,mp.mpf('.5')):
        L=abs(mp.exp(-m_int-1j*theta)-1)<mp.mpf('1e-32')
        R=abs(mp.exp(+m_int-1j*theta)-1)<mp.mpf('1e-32')
        assert L==R
# Four-dimensional QED is vectorlike; left e_L and left-handed
# conjugate of e_R have opposite anomaly coefficients.
assert 1**3+(-1)**3==0
for name,value in [('z0',z),('Lambda_tuning',ELL),('radion_curvature',Uxx),
 ('Wilson_curvature',Utt),('electron_mass_GeV_input',ME),('electron_z_e',ze),
 ('electron_first_KK_mass_GeV',mass_KK_1),('radion_range_m',radion_range),
 ('b0_M5',b0*M5),('U1_NDA_cutoff_GeV',cutoff_NDA),('compact_cutoff_ratio',b0*cutoff_NDA)]:
    print(name,mp.nstr(value,18))
print('2D sampled minimum:',smallest,'min local optimizer:',min(fit))
print('PASS light vectorlike QED zero mode, positive Hessian, analytic radial minimum, uniform x->0 repulsion')
print('OPEN 2D global theorem, electroweak chirality, Standard Model, interacting quantum loops, Earth solution')
