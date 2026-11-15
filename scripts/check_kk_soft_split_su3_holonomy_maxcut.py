#!/usr/bin/env python3
"""Conditional 5D S1 KK QED+QCD paired-sector vacuum and SU3 global Wilson cut.

ORIGINAL PRIOR PHYSICS: 5D N=1 vector multiplet A5,real adjoint scalar,
adjoint symplectic Majorana gaugino (3+1=4 boson vs 4 fermion d.o.f);
hypermultiplet Dirac + two complex scalars (4 vs 4 d.o.f).
Ponton/Poppitz JHEP06(2001)019; 5D SUSY field-content sources; Abe et al.
PTEP 2014 073B04 for charged periodic KK Wilson/radion determinants.

This is an explicitly FREE one-loop split-mass determinant, NOT a complete
interacting anomaly-free/broken-SUSY action or physical 5D Standard Model.
"""
import numpy as np
from mpmath import mp
mp.dps=34
Z=mp.zeta(5)
b=mp.mpf('1e-24')/mp.mpf('0.1973269804e-15')
ms=mp.mpf('3000');mvec=mp.mpf('4000');mex=mp.mpf('9000')
ze=2*mp.pi*mp.mpf('0.00051099895')*b
zS=2*mp.pi*ms*b;zG=2*mp.pi*mvec*b;zA=zG;zX=2*mp.pi*mex*b
zq=[2*mp.pi*mp.mpf(s)*b for s in ('.00216','.00470','.0935','1.273','4.183','172.56')]
charges=[mp.mpf(2)/3,-mp.mpf(1)/3,-mp.mpf(1)/3,mp.mpf(2)/3,-mp.mpf(1)/3,mp.mpf(2)/3]
exotic_charges=[mp.mpf(2)/3,-mp.mpf(1)/3]
assert 6+len(exotic_charges)==8  # Necessary SU3 fundamental parity-anomaly count only

def f(z,phase=0,der='f'):
    e=mp.exp(-z+1j*phase)
    if z==0 and der=='tt':return -mp.re(mp.polylog(3,e))/Z
    if z==0 and der=='z':return mp.mpf(0)
    if der=='f':out=mp.polylog(5,e)+z*mp.polylog(4,e)+z*z*mp.polylog(3,e)/3
    elif der=='z':out=-z*(mp.polylog(3,e)+z*mp.polylog(2,e))/3
    elif der=='zz':out=-(mp.polylog(3,e)+z*mp.polylog(2,e)-z*z*mp.polylog(1,e))/3
    elif der=='tt':out=-(mp.polylog(3,e)+z*mp.polylog(2,e)+z*z*mp.polylog(1,e)/3)
    else:raise ValueError(der)
    return mp.re(out)/Z

def h(z):return f(z)-z*f(z,der='z')/5
def omega(z):return z*z*f(z,der='zz')-4*z*f(z,der='z')
def d(z):
    return (9-4*h(z)-4*h(4*z)-4*h(ze))*5 + \
       8*(15+5*h(zA)-20*h(zG)) + \
       12*mp.fsum(-5*h(q)+5*h(zS) for q in zq) + \
       12*len(exotic_charges)*(-5*h(zX)+5*h(zS))
z=mp.findroot(d,(mp.mpf('.7'),mp.mpf('1.2')))
W0=-9+4*f(z)+4*f(4*z)+4*f(ze)+8*(-3-f(zA)+4*f(zG))+\
    12*mp.fsum(f(q)-f(zS) for q in zq)+12*len(exotic_charges)*(f(zX)-f(zS))
ell=-W0
assert ell>0 and abs(d(z))<mp.mpf('1e-28')
Uxx=4*(omega(z)+omega(4*z)+omega(ze))+8*(-omega(zA)+4*omega(zG))+\
     12*mp.fsum(omega(q)-omega(zS) for q in zq)+\
     12*len(exotic_charges)*(omega(zX)-omega(zS))
Utt_em=4*f(4*z,der='tt')-8*f(z,der='tt')+4*f(ze,der='tt')+\
     12*mp.fsum(Q*Q*(f(q,der='tt')-f(zS,der='tt')) for q,Q in zip(zq,charges))+\
     12*sum(Q*Q for Q in exotic_charges)*(f(zX,der='tt')-f(zS,der='tt'))
Cg=-3*f(0,der='tt')-f(zA,der='tt')+4*f(zG,der='tt')
Cf=4*mp.fsum(f(q,der='tt')-f(zS,der='tt') for q in zq)+\
   4*len(exotic_charges)*(f(zX,der='tt')-f(zS,der='tt'))
Utt_colour=6*Cg+Cf  # orthonormal traceless SU3 Cartan modes
assert Uxx>0 and Utt_em>0 and Utt_colour>0

# Direct high-precision colour-centre discriminator; adjoint gauge phases
# remain trivial for a centre element, fundamental quarks do not.
p=2*mp.pi/3
def Fcentre(z):return f(z,p)-f(z,0)
centre_without_exotics=12*mp.fsum(Fcentre(q)-Fcentre(zS) for q in zq)
centre_cost=centre_without_exotics+12*len(exotic_charges)*(Fcentre(zX)-Fcentre(zS))
assert centre_without_exotics<0 and centre_cost>0

# ANALYTIC ALL-COLOR-HOLONOMY result at x=1, theta_EM=0:
# one fundamental-colour phase φ has Fourier coefficients c_n.
# c1<0, Σ_(n>=2)n |c_n|<|c1| implies F'(φ)>0 for 0<φ<π,
# since |sin(nφ)|<=n sin φ. Even periodicity gives unique min φ=0.
# Adjoint gauge coefficients are 3(a_n(zG)-a_n(0))<0, so
# each cos(n(φ_i-φ_j)) is separately minimized at aligned colors.
N=800
n=np.arange(1,N+1,dtype=np.float64)
def coeff(zz):
    t=n*float(zz)
    return np.exp(-t)*(1+t+t*t/3)/(n**5*float(Z))
baseC=4*coeff(4*z)-8*coeff(z)+4*coeff(ze)
gaugeC=-3*coeff(0)-coeff(zA)+4*coeff(zG)
quarkC=[4*(coeff(q)-coeff(zS)) for q in zq]
exoticC=4*(coeff(zX)-coeff(zS))
fundC=np.sum(np.asarray(quarkC),axis=0)+len(exotic_charges)*exoticC
assert np.all(gaugeC<0) and fundC[0]<0
prefix=float(np.sum(n[1:]*np.abs(fundC[1:])))
# k(s)=e^-s(1+s+s²/3), |k'(s)|=s(1+s)e^-s/3<=s/3.
# Thus |k(na)-k(nb)|<=n²|a²-b²|/6 and
# Σ_(n>N) n|c_n| <= (2/(3ζ5)) A/N.
A=float(sum(abs(q*q-zS*zS) for q in zq)+
        len(exotic_charges)*abs(zX*zX-zS*zS))
infinite_tail_upper=(2/(3*float(Z)))*A/N
strict_margin=abs(fundC[0])-prefix-infinite_tail_upper
assert strict_margin>1e-8

# Joint angular survey: theta_EM=0,2π,4π, 31x31 SU3 Cartan grid.
# Charge 1/3 implies 6π EM fundamental period unless accompanied
# by colour-centre quotient; this is NOT an all-theta continuum proof.
def angle_cost(t,c1,c2):
    c=np.array([c1,c2,-c1-c2])
    ph=np.array([c[i]-c[j] for i in range(3) for j in range(3) if i!=j])
    v=np.sum(baseC*(np.cos(n*t)-1))
    v+=np.sum(gaugeC*np.sum(np.cos(np.outer(n,ph))-1,axis=1))
    for Q,K in zip(charges,quarkC):
        v+=np.sum(K*np.sum(np.cos(np.outer(n,c+float(Q)*t))-1,axis=1))
    for Q in exotic_charges:
        v+=np.sum(exoticC*np.sum(np.cos(np.outer(n,c+float(Q)*t))-1,axis=1))
    return float(v)
lowest=(float('inf'),0,0,0)
for t in (0.0,2*np.pi,4*np.pi):
    for c1 in np.linspace(-np.pi,np.pi,31):
        for c2 in np.linspace(-np.pi,np.pi,31):
            v=angle_cost(t,c1,c2)
            if v<lowest[0]:lowest=(v,t,c1,c2)
assert lowest[0]>-1e-10 and abs(angle_cost(2*np.pi,2*np.pi/3,2*np.pi/3))<1e-11

for name,value in [
    ('inverse_radius_GeV',1/b),('radion_z',z),('bulk_tuning_ell',ell),
    ('stationarity_D',d(z)),('radion_Uxx',Uxx),
    ('EM_Wilson_Utt',Utt_em),('SU3_Cartan_Utt',Utt_colour),
    ('SU3_centre_gap_without_exotics',centre_without_exotics),
    ('SU3_centre_gap_with_even_exotics',centre_cost),
    ('fundamental_first_harmonic',fundC[0]),
    ('fundamental_finite_tail',prefix),
    ('fundamental_infinite_tail_bound',infinite_tail_upper),
    ('strict_first_harmonic_margin',strict_margin),
    ('exotic_fermion_mass_GeV',mex),
    ('partner_scalar_mass_GeV',ms),
    ('adjoint_partner_mass_GeV',mvec),
    ('sampled_joint_phase_min',lowest[0])]:
    print(name,mp.nstr(value,17) if isinstance(value,mp.mpf) else value)
print('PASS local joint radion+EM+colour Hessian and analytic-tail global SU3 identity minimum at theta_EM=0, x=1')
print('SAMPLED full EM-colour phases; global full (x,EM,colour) minimum, 5D interacting soft SUSY, Chern-Simons and SM CHIRALITY OPEN')
