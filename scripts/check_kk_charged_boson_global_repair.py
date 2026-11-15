#!/usr/bin/env python3
"""One-loop KK S1 charged complex scalar repair (conditional EFT).
Free-field counts: 5D gravity/Maxwell/real scalar -9; three neutral
massive Dirac +12; charged massive Dirac +4; charged massive complex
scalar -2. Mass ratios mD/mN=4 and mB/mN=1. No classical condensates.
Tests joint radion/Wilson Hessian, small-b uniform repulsion and a
bounded landscape scan; NOT a certified global minimum/real Earth model.
"""
from mpmath import mp
from scipy.optimize import minimize
import numpy as np
mp.dps=50
N=120
Z=mp.zeta(5)
C=3*Z/(64*mp.pi**6)
a,d,q,bos,kq,kb=9,12,4,2,mp.mpf(4),mp.mpf(1)
HC=mp.mpf('0.1973269804e-15')
MP=mp.mpf('2.435e18')
b=mp.mpf('1e-24')/HC
e=mp.sqrt(4*mp.pi/mp.mpf('137.035999084'))

def f(z,t=mp.mpf(0),kind=0):
    terms=[]
    for n in range(1,N+1):
        nz=n*z; p=mp.exp(-nz); co=mp.cos(n*t); si=mp.sin(n*t)
        if kind==0: v=p*(1+nz+nz*nz/3)*co/n**5
        elif kind==1: v=-z*p*(1+nz)*co/(3*n**3)
        elif kind==2: v=-p*(1+nz-nz*nz)*co/(3*n**3)
        elif kind==3: v=-p*(1+nz+nz*nz/3)*si/n**4
        elif kind==4: v=-p*(1+nz+nz*nz/3)*co/n**3
        else: raise ValueError
        terms.append(v)
    return mp.fsum(terms)/Z

def h(z,t=0): return f(z,t)-z*f(z,t,1)/5
z=mp.findroot(lambda v:d*h(v)+q*h(kq*v)-bos*h(kb*v)-a,(mp.mpf(1),mp.mpf('1.5')))
L=a-d*f(z)-q*f(kq*z)+bos*f(kb*z)
def U(x,t):
    return L/x+(-a+d*f(z*x)+q*f(kq*z*x,t)-bos*f(kb*z*x,t))/x**6

def radial_term(weight,j,t=0):
    return weight*((j*z)**2*f(j*z,t,2)-4*j*z*f(j*z,t,1))
Uxx=radial_term(d,1)+radial_term(q,kq)-radial_term(bos,kb)
Utt=q*f(kq*z,0,4)-bos*f(kb*z,0,4)
assert L>0 and Uxx>0 and Utt>0
assert abs(U(1,0))<mp.mpf('1e-44')
assert abs(mp.diff(lambda x:U(x,0),1))<mp.mpf('1e-43')
assert abs(mp.diff(lambda t:U(1,t),0))<mp.mpf('1e-43')
assert abs(mp.diff(lambda x:U(x,0),1,2)-Uxx)<mp.mpf('1e-43')
assert abs(mp.diff(lambda t:U(1,t),0,2)-Utt)<mp.mpf('1e-43')
# UV collapse repaired for ALL theta:
# as x->0, -9+12+(4-2)f(0,theta)=3+2f(0,theta)>=1.
# Bound |f(0,theta)|<=1 follows from positive n^-5 coefficients.
assert -a+d-(q-bos)==1
# At x=1, harmonic derivative dominance makes theta=0 global min.
def harmonic(n,w):
    y=n*w
    return mp.exp(-y)*(1+y+y*y/3)/(Z*n**5)
first=bos*harmonic(1,kb*z)-q*harmonic(1,kq*z)
tail=mp.fsum(n*n*abs(bos*harmonic(n,kb*z)-q*harmonic(n,kq*z))
             for n in range(2,N+1))
assert first>tail>0
# Scan finite landscape AND locally optimize from many points.
# Double-precision vectorised scan is exploratory; stationarity uses mpmath.
nfloat=np.arange(1,N+1,dtype=float)
def ffast(w,t):
    nw=nfloat*w
    return float(np.sum(np.exp(-nw)*(1+nw+nw*nw/3)*np.cos(nfloat*t)/nfloat**5)/float(Z))
def fast_U(x,t):
    return float(L)/x+(-a+d*ffast(float(z)*x,0)+q*ffast(float(kq*z)*x,t)-bos*ffast(float(kb*z)*x,t))/x**6
minimum=(float('inf'),0,0)
for xx in np.geomspace(.0001,1000,260):
    for tt in np.linspace(0,float(mp.pi),49):
        val=fast_U(float(xx),float(tt))
        if val<minimum[0]: minimum=(val,xx,tt)
assert minimum[0]>-1e-9
def fun(v): return fast_U(float(np.exp(v[0])),float(v[1]))
starts=[(float(np.log(x)),float(t)) for x in (.2,.5,.85,1,1.3,2,5)
        for t in (0,float(mp.pi)/2,float(mp.pi))]
fits=[minimize(fun,v,method='L-BFGS-B',bounds=[(-4,5),(0,float(mp.pi))],
               options={'maxiter':60}) for v in starts]
assert min(r.fun for r in fits)>-1e-7
rad_range=HC*MP*b*b/mp.sqrt(2*C*Uxx/3)
fTheta=1/(2*mp.pi*b*e)
wilson_range=HC*fTheta/mp.sqrt(C*Utt/b**4)
M5=(MP**2/(2*mp.pi*b))**(mp.mpf(1)/3)
assert b*M5>1000 and rad_range<mp.mpf('1e-10')
for name,value in [('z_neutral',z),('bulk_tuning',L),('radion_Uxx',Uxx),
 ('Wilson_Utt',Utt),('phase_tail_over_first',tail/first),
 ('radion_range_m',rad_range),('Wilson_range_m',wilson_range),
 ('charged_scalar_bulk_mass_GeV',kb*z/(2*mp.pi*b)),
 ('charged_fermion_bulk_mass_GeV',kq*z/(2*mp.pi*b)),
 ('small_radius_uniform_U_coefficient_lower_bound',1)]:
    print(name,mp.nstr(value,16))
print('landscape_grid_min',minimum,'optimizer_min',min(r.fun for r in fits))
print('PASS local Minkowski, Hessian, global theta min at x=1, UV repulsion for all theta')
print('SAMPLED no deeper minimum on finite landscape; all-radius global theorem OPEN')
print('FAIL observed light chiral charged matter; NO full 5D Earth stress or Agda kernel proof')
