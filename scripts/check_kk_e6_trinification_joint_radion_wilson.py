#!/usr/bin/env python3
"""Fuller KK QED/QCD/E6 candidate: same radion + Maxwell Wilson Hessian.

Use the actual selected PR #1241 smooth periodic S1 free-spectrum:
- base -9: graviton, independent Maxwell, massless neutral real scalar
- neutral heavy Dirac +12, charged heavy Dirac +4, charged heavy
  complex bosons -8, light charged electron Dirac +4
- QCD gluons -24, 6 light vectorlike triplet quarks +72
- two extra UNBROKEN SU3 octets -48 (5D MASSLESS vectors: 3 pol each)
All six quarks carry physical Q_EM = (+2/3,-1/3,-1/3,+2/3,
-1/3,+2/3), not zero. This can restore RADION stationarity by
retuning the neutral bulk mass but fails the Wilson curvature.
Prior original roots: Slansky 1981 E6->SU3^3 branching (group only),
Abe et al 2014 one-loop periodic KK Casimir with Wilson phase.
No physical E6 action, EW breaking, SM chirality or 5D Earth.
"""
from mpmath import mp
from math import ceil
mp.dps=48
Z5=mp.zeta(5)
HBARC=mp.mpf('0.1973269804e-15')
b0=mp.mpf('1e-24')/HBARC
me=mp.mpf('0.00051099895')
ze=2*mp.pi*me*b0
masses=[mp.mpf(t) for t in ('.00216','.00470','.0935','1.273','4.183','172.56')]
charges=[mp.mpf(2)/3,-mp.mpf(1)/3,-mp.mpf(1)/3,
         mp.mpf(2)/3,-mp.mpf(1)/3,mp.mpf(2)/3]
zq=[2*mp.pi*m*b0 for m in masses]
def f(z,theta=0,kind='value'):
    u=mp.exp(-z+1j*theta)
    if kind=='value':
        out=mp.polylog(5,u)+z*mp.polylog(4,u)+z*z*mp.polylog(3,u)/3
    elif kind=='z':
        out=-z*(mp.polylog(3,u)+z*mp.polylog(2,u))/3
    elif kind=='zz':
        out=-(mp.polylog(3,u)+z*mp.polylog(2,u)-z*z*mp.polylog(1,u))/3
    elif kind=='thetatheta':
        out=-(mp.polylog(3,u)+z*mp.polylog(2,u)+
              z*z*mp.polylog(1,u)/3)
    else:raise ValueError(kind)
    return mp.re(out)/Z5
def h(z):return f(z)-z*f(z,kind='z')/5
def omega(z):return z*z*f(z,kind='zz')-4*z*f(z,kind='z')
assert 78==3*8+2*27
assert 248==78+8+2*27*3
assert 16*3==48  # additional 2 octets, massless 5D gauge fields

# Original QED-only stationary solution, then QCD+two dark octets.
old=mp.findroot(lambda z:4*h(z)+4*h(4*z)+4*h(ze)-9,(mp.mpf('.7'),mp.mpf('1.2')))
z=mp.findroot(lambda z:4*h(z)+4*h(4*z)+4*h(ze)+
                         12*mp.fsum(h(q) for q in zq)-81,
              (mp.mpf('.7'),mp.mpf('1.2')))
# QCD quark coefficient 12=3 colours*4 Dirac, and U1 charge q enters
# the phase only, as theta -> q*theta, not the radial determinant at theta=0.
def W(x,theta):
    neutral=12*f(z*x)
    charged=(4*f(4*z*x,theta)-8*f(z*x,theta)
             +4*f(ze*x,theta))
    quarks=12*mp.fsum(f(q*x,charge*theta)
                      for q,charge in zip(zq,charges))
    return -81+neutral+charged+quarks
ell=-W(mp.mpf(1),mp.mpf(0))
def U(x,theta):return ell/x+W(x,theta)/x**6
uxx=(4*omega(z)+4*omega(4*z)+4*omega(ze)
     +12*mp.fsum(omega(q) for q in zq))
qed_utt=4*f(4*z,kind='thetatheta')-8*f(z,kind='thetatheta')+4*f(ze,kind='thetatheta')
qcd_utt=12*mp.fsum(charge**2*f(q,kind='thetatheta')
                    for q,charge in zip(zq,charges))
utt=qed_utt+qcd_utt
assert abs(U(1,0))<mp.mpf('1e-40')
assert abs(mp.diff(lambda x:U(x,0),1))<mp.mpf('1e-38')
assert abs(mp.diff(lambda x:U(x,0),1,2)-uxx)<mp.mpf('1e-32')
assert abs(mp.diff(lambda theta:U(1,theta),0,2)-utt)<mp.mpf('1e-32')
assert ell>0 and uxx>0 and qed_utt>0 and qcd_utt<0 and utt<0
assert U(1,mp.mpf('.001'))<U(1,mp.mpf(0))
assert abs(z-old)<mp.mpf('1e-8')

# Needed charged-boson WILSON curvature repair:
# a periodic massless unit-charge real DOF would give +zeta3/zeta5
# to Utt, but a nontrivially U1 charged scalar must be COMPLEX
# (minimum two real degrees). A neutral singlet contributes ZERO
# Wilson curvature, no matter how many neutral free fields are added.
unit=mp.zeta(3)/Z5
min_real_units=ceil(float(-utt/unit))
min_complex_scalars=ceil(min_real_units/2)
assert min_real_units==19 and min_complex_scalars==10
assert utt+18*unit<0 and utt+20*unit>0
for name,val in [('old_neutral_z',old),('selected_z_with_two_extra_SU3',z),
                 ('neutral_z_shift',z-old),('tuned_ell',ell),
                 ('U_radion_curvature',uxx),('U_QED_Wilson_curvature',qed_utt),
                 ('U_quark_Wilson_curvature',qcd_utt),
                 ('U_total_Wilson_curvature',utt),
                 ('theta_bound_light_electron',ze),
                 ('unit_charge_real_scalar_Wilson_curvature_upper',unit)]:
    print(name,mp.nstr(val,20))
print('minimum_extra_massless_charged_real_polarizations',min_real_units)
print('minimum_extra_unit_charge_complex_scalar_fields',min_complex_scalars)
print('PASS stationary flat radion vacuum in free SU3^3 massless vector toy')
print('FAIL photon Wilson phase theta=0: 2D Hessian saddle, quark loops dominate')
print('FAIL neutral Higgs singlet portal: zero direct EM Wilson-phase curvature')
print('BOUNDARY charged bosons also change radion stationarity, so 10 complex')
print('        scalars are a SINGLE-CONSUMER bound, not a joint solution')
print('BOUNDARY 5D HIGGSED massive vectors have FOUR polarizations,')
print('        so scalar-like 86GeV mass tuning cannot be imported as 3-pol vector')
print('OPEN 5D E6 breaking/action, all gauge/ghost/Higgs loops, EW chirality, empirical viability')
