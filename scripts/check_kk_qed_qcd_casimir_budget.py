#!/usr/bin/env python3
"""Selected KK S1 QED->QCD vacuum-consumer nontransport, not full QCD.

Free 5D SU3 gluons: 8*3 = -24 Casimir units.
Six 5D Dirac quark flavours, 3 colours: 6*3*4 = +72 units.
Smooth periodic S1, trivial photon/colour Wilson phases, b0=1e-24m.
PDG 2025 low-scale quark masses are illustrative inputs only; the
rigorous bound uses ALL masses <=200GeV, not a mass-running claim.
Abe et al. (2014), DOI 10.1093/ptep/ptu097: free KK Casimir framework.
"""
from mpmath import mp
mp.dps=45
HBARC=mp.mpf("0.1973269804e-15")
b0=mp.mpf("1e-24")/HBARC
z=mp.mpf("0.9081569907830750")
me=mp.mpf("0.00051099895")
quarks={"u":"0.00216","d":"0.00470","s":"0.0935",
        "c":"1.2730","b":"4.183","t":"172.56"}
Z=mp.zeta(5)
def f(s):
    u=mp.exp(-s)
    return (mp.polylog(5,u)+s*mp.polylog(4,u)+s*s*mp.polylog(3,u)/3)/Z
def fp(s):
    u=mp.exp(-s)
    return -s*(mp.polylog(3,u)+s*mp.polylog(2,u))/(3*Z)
def boundloss(s):
    return s*s*mp.zeta(3)/(6*Z)+s**3*mp.zeta(2)/(9*Z)
ze=2*mp.pi*me*b0
W0=-9+4*f(z)+4*f(4*z)+4*f(ze)
W0p=4*z*fp(z)+16*z*fp(4*z)+4*ze*fp(ze)
assert abs(W0p-5*W0)<mp.mpf("1e-12")
# Compare SAME compactification (b0), source fields, and theta=0.
qs=[2*mp.pi*mp.mpf(m)*b0 for m in quarks.values()]
gluon_units=-8*3
quark_units=6*3*4
assert (gluon_units,quark_units)==(-24,72)
dW=gluon_units+12*mp.fsum(f(q) for q in qs)
dWp=12*mp.fsum(q*fp(q) for q in qs)
delta=dWp-5*dW
assert abs(delta+240)<mp.mpf("1e-6")
# For ALL six 5D free Dirac quark masses <=200GeV:
# f(s)>=1-loss(s), f'(s)<=0 for s>=0.
limit=2*mp.pi*mp.mpf("200")*b0
loss=boundloss(limit)
assert all(q<limit for q in qs) and loss<mp.mpf("1e-10")
lower_dW=gluon_units+quark_units*(1-loss)
upper_delta=-5*lower_dW
assert delta<=upper_delta<mp.mpf("-239.999999")
# Since U=ell/x+W(x)/x^6, U(1)=U'(1)=0
# requires W'(1)-5W(1)=0, INDEPENDENT of ell.
ell_old=-W0
ell_with_colour=-(W0+dW)
assert ell_old>0 and ell_with_colour<0
assert abs(W0p+dWp-5*(W0+dW)-delta)<mp.mpf("1e-12")
# A nontrivial SU3 centre Wilson phase shifts fundamental n by 1/3,
# removing light quark zero modes; similarly QED theta lifts electron.
assert 1/(3*b0)>mp.mpf("1e7")
assert 2*mp.pi*me*b0<mp.mpf("2e-11")
# Illustrative one-loop 4D QCD running (no threshold matching or 5D loops).
alpha_mZ=mp.mpf("0.118")
beta0=11-mp.mpf(2)*6/3
alpha_hi=alpha_mZ/(1+alpha_mZ*beta0/(2*mp.pi)*mp.log((1/b0)/mp.mpf("91.1876")))
assert mp.mpf(".03")<alpha_hi<mp.mpf(".06")
for name,val in (
 ("1/b0_GeV",1/b0),("W_original",W0),("deltaW_from_QCD",dW),
 ("delta_compatibility",delta),("rigorous_upper_delta",upper_delta),
 ("ell_original",ell_old),("ell_for_zero_energy_after_QCD",ell_with_colour),
 ("stationary_residual_QCD",W0p+dWp-5*(W0+dW)),
 ("SU3_centre_zero_mode_gap_GeV",1/(3*b0)),
 ("electron_light_theta_scale",2*mp.pi*me*b0),
 ("indicative_alpha_s_1overb0",alpha_hi)
): print(name,mp.nstr(val,19))

# BIDI repair Pareto: at the SAME radius, free periodic REAL bosonic
# polarizations contribute at most +5 each to the compatibility residual.
# No extra fermion or 5D model change allowed in this restricted comparison.
def h(s):
    return f(s)-s*fp(s)/5
assert abs(h(mp.mpf('0'))-1)<mp.mpf('1e-40')
for s in map(mp.mpf,('0.00001','0.5','1','3','10')):
    assert 0<h(s)<1
assert delta+47*5<0
repair_mass_parameter=mp.findroot(
    lambda v:48*5*h(v)+delta,
    (mp.mpf('1e-6'),mp.mpf('1e-5')))
assert repair_mass_parameter>0
assert abs(48*5*h(repair_mass_parameter)+delta)<mp.mpf('1e-35')
print("minimum_added_free_periodic_real_boson_units_same_radius",48)
print("illustrative_48_boson_mass_GeV",
      mp.nstr(repair_mass_parameter/(2*mp.pi*b0),16))
print("WARNING 48 unexplained light scalar polarizations are not an established physical model")

print("PASS restricted same-radius, zero-holonomy QCD vacuum no-go")
print("NO claim about arbitrary KK spectra, interacting QCD, chirality or Earth.")
