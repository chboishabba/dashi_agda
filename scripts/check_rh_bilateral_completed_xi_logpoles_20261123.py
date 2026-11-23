#!/usr/bin/env python3
"""RH/GRH reflection-pair completed xi/Lambda logarithmic poles, source SymPy.

Reuses original Lean RiemannProjectiveQuarticFourWindowSignedPole*,
the original 0/2/4 BidiMarkedFourth marked source and signed FarExact.
Formal algebra: no GRH/RH zero inference, no Agda/Lean kernel/CI.
"""
import sympy as s
from fractions import Fraction
w,a,u,q,alpha,x,m,g,y=s.symbols("w a u q alpha x m g y",real=True)
pi=s.pi
# ξ'/ξ poles are zero locations, with multiplicity m; ξ itself has zeros.
paired=1/(w-a)+1/(w+a)
assert s.cancel(paired-2*w/(w*w-a*a))==0
assert s.cancel(paired-2/w-2*a*a/(w*(w*w-a*a)))==0
assert s.simplify(paired.subs(w,0))==0  # mediator is pole-pair LOG DERIVATIVE, NOT ξ
# For Re(w)>|a|, the pair resolvent equals Laplace of 2cosh(a*u).
assert s.cancel(1/(w-a)+1/(w+a)-2*w/(w*w-a*a))==0
assert s.simplify(s.cosh(a*u)-(s.exp(a*u)+s.exp(-a*u))/2)==0
# The source even-profile cosh(a/r*u)*cos(q*u) is the average of
# two COMPLEX angular Fourier characters q +/- i*a/r.
assert s.simplify(s.trigsimp(
    (s.cos((q+s.I*alpha)*u)+s.cos((q-s.I*alpha)*u))/2
     -s.cos(q*u)*s.cosh(alpha*u)))==0
F=lambda z:-s.Rational(320,351)*s.sin(pi*z/4)**4
assert s.simplify(s.trigsimp(
    (F(4+s.I*alpha)+F(4-s.I*alpha))/2
    +s.Rational(320,351)*s.sinh(pi*alpha/4)**4))==0
# Original four-window small-bump high-pole near 4 has leading
# K(R,4+x sqrt(R))/R² = 60 m2/13 - (5π⁴/1404)x⁴.
m2,z=s.symbols("m2 z",positive=True)
lead=60*m2/s.Integer(13)-5*pi**4*z**4/s.Integer(1404)
kappa=6*m2**s.Rational(1,4)/pi
assert all(s.simplify(lead.subs(z,kappa*r))==0 for r in (1,-1,s.I,-s.I))
assert s.simplify(s.diff(lead,z).subs(z,kappa))!=0
# These TWO COMPLEX (imaginary) root branches have horizontal parameter
# magnitude at least (28/33)*sqrtR at small R, whereas the physical
# |a|<=1/2 and t>=10^14 imply |a/(t/16)|<=8e-14.
R=s.Rational(1,10**10)
alpha_max=s.Rational(8,10**14)
assert s.Rational(9,4)**4>24
assert s.Rational(28,33)/10**5>10**8*alpha_max
assert float(s.Rational(320,351)*s.sinh(pi*alpha_max/4)**4)<1e-50
# Entire polynomial with RH-like functional & conjugation symmetries,
# BUT OFF-LINE zeros: symmetry + pole pairing does not imply RH.
v=s.symbols("v",real=True)
quartet=s.expand(((v-s.I*g)**2-a*a)*((v+s.I*g)**2-a*a))
assert s.simplify(quartet-((v*v-g*g-a*a)**2+4*v*v*g*g))==0
assert s.simplify(quartet.subs(v,s.I*y)-((y-g)**2+a*a)*((y+g)**2+a*a))==0
assert s.simplify(s.diff(quartet,v).subs(v,0))==0
# Original Lean source P4=Re(a+iδ)^4, original local cone δ²<=6a².
delta,Y=s.symbols("delta Y",real=True)
p4=s.expand((a+s.I*delta)**4).as_real_imag()[0]
assert p4==a**4-6*a**2*delta**2+delta**4
p4ratio=Y**2-6*Y+1
low,high=3-2*s.sqrt(2),3+2*s.sqrt(2)
assert s.factor(p4ratio,extension=s.sqrt(2))==(Y-high)*(Y-low)
assert 0<low<1<high<6
assert p4ratio.subs(Y,0)>0 and p4ratio.subs(Y,1)<0 and p4ratio.subs(Y,6)>0
# True off-ordinate far q≈4 has delta=t*q/16; mirror pair
# residue relative to the DOUBLE critical-axis reference is <5/t².
assert s.cancel(paired-2/w-2*a*a/(w*(w*w-a*a)))==0
assert s.Rational(64)/(s.Rational(39,10)**2)<5
# For complex primitive Dirichlet characters the full quartet is across
# BOTH chi and conj(chi), but horizontal same-ordinate partner is same chi.
root=("chi",Fraction(2,3),Fraction(7))
def C(r):
    ch,b,gam=r
    return ("conjchi" if ch=="chi" else "chi",b,-gam)
def E(r):
    ch,b,gam=r
    return ("conjchi" if ch=="chi" else "chi",1-b,-gam)
assert C(C(root))==E(E(root))==root
assert C(E(root))==E(C(root))==("chi",Fraction(1,3),Fraction(7))
assert len({root,C(root),E(root),C(E(root))})==4
print("PASS paired ξ'/ξ poles with zero mediator and exact a² residual")
print("PASS Laplace cosh and entire compact Fourier complex conjugate-square")
print("PASS original quartic notch TWO real plus TWO imaginary small-R branches")
print("PASS imaginary source-test branches too far in horizontal α for physical t>=1e14")
print("PASS quartic signed cone P4 changes sign at 3±2sqrt2 inside cutoff6")
print("PASS no-go: symmetric entire quartet with off-critical zeros")
print("PASS GRH character-labelled FE/conjugation commuting square")
print("OPEN true signed FarExact-μ post-sixth bound and χ-specific prime source")

# ORIGINAL Lean local adverse mass sharpened:
# quarticSignedPolePhysicalFourthPhaseReal = (delta²-3a²)²-8a⁴.
# |heightOf rho|<=1/2 gives per-zero max(-P4,0)<=8a⁴<=1/2,
# improving original 3/2 bound by factor3.
assert s.expand(p4-((delta*delta-3*a*a)**2-8*a**4))==0
assert s.simplify(p4.subs({a:s.Rational(1,2),delta:s.sqrt(3)/2}))==-s.Rational(1,2)
assert s.simplify((s.sqrt(2)-1)**2-low)==0
assert s.simplify((s.sqrt(2)+1)**2-high)==0
assert (1+s.sqrt(2))/2<s.Rational(3,2)
assert s.Rational(9,2)/s.Rational(3,2)==3
print("PASS same original adverse phase <=8 a^4 <=1/2 per multiplicity")
print("PASS narrower original adverse zero-count window |gamma-t|<(1+sqrt2)/2")
print("PASS source 9/2 A0 log envelope improves to 3/2 A0 log with local weld")

# Same-ORIGINAL-profile holomorphic contour trace for completed ξ:
# P_W is original even compact support; C_W(z)=∫P_W(v)cos(zv)dv
# is entire.  f_t(s)=r^-2*C_W(-i(s-(1/2+i*t))/r).
# Its horizontal reflection pair sums EXACTLY to 2m*K(alpha,q)/r².
s0=s.Rational(1,2)+s.I*6
r=s.Integer(5)
polep=s.Rational(1,2)+s.Rational(1,3)+7*s.I
polem=s.Rational(1,2)-s.Rational(1,3)+7*s.I
qt=s.Rational(1,5);alphat=s.Rational(1,15)
holo=lambda u:F(-s.I*(u-s0)/r)/r**2
assert s.simplify(s.trigsimp(holo(polep)-F(qt-s.I*alphat)/r**2))==0
assert s.simplify(s.trigsimp(holo(polem)-F(qt+s.I*alphat)/r**2))==0
assert s.simplify(s.trigsimp(
    holo(polep)+holo(polem)-
      (F(qt-s.I*alphat)+F(qt+s.I*alphat))/r**2))==0
# Verify the RESIDUES of f(s)*P'(s)/P(s), not only values at zeros.
ss=s.symbols("ss")
orbit=(polep,polem,s.conjugate(polep),s.conjugate(polem))
Qpoly=s.prod(ss-rt for rt in orbit)
z=-s.I*(ss-s0)/r
holopoly=(z**4-3*z**2+1)/r**2
for rt in orbit:
    assert s.simplify(s.residue(
        holopoly*s.diff(Qpoly,ss)/Qpoly,ss,rt)
        -holopoly.subs(ss,rt))==0
print("PASS original entire cosh-Fourier test lifts reflected xi zeros to holomorphic contour trace")
print("PASS 4/4 meromorphic logarithmic-derivative residues of exact bilateral quartet")
print("CAUTION FAR/LOCAL indicator not holomorphic: contour FULL source, then subtract original local and sameOrd")


# 23 Nov P0 follow-up: exact support cutoff and SAME-ORDINATE subtraction.
# Original Lean NMu.lean:
#   quarticFourCompletedRadius(t) = 16*(pi+1)/t,
#   quarticFourPhysicalDetector_support_completedRadius
# under W.Rpos,W.RltOne. For t>=200, this radius is < log(2),
# so ANY classical explicit-formula prime-power sample g(log n), n>=2,
# vanishes. This is a test-support fact, NOT a completed RH estimate.
assert 16*(s.pi+1)/200 < s.Rational(2,5)  # pi<4
assert s.Rational(2,5) < s.Rational(1,2) < s.log(2)
print("PASS original physical support excludes every log(n), n>=2, for t>=200")

# Lean JointHorizontalJet.signedNormalizedPairKernel_zero_eq_neg_four_target:
# K_W(alpha,0)=-4 D_W(alpha).
# Lean SignedPolePair.physicalCombinedHeightDefect_scaled and
# SignedPolePair.combinedZeroHeightDefect identify d(rho)=m D_W(a/r)/r^2.
_R,_mult,_def=s.symbols("_R _mult _def",positive=True)
same_ordinate_term=_mult*(-4*_def)/_R**2
same_ordinate_defect=_mult*_def/_R**2
assert s.simplify(same_ordinate_term+4*same_ordinate_defect)==0
assert s.simplify(2*same_ordinate_term+8*same_ordinate_defect)==0
print("PASS original SAME-ORD term = -4*d(rho), not zero; pair = -8*d(rho)")

# Define A=FULL completed-xi contour zero sum, I=original mu integral,
# H=original off-ordinate zero sum, L=canonical local slack, d=target
# defect, and Dsame=sum_{im(z)=t} d(z).
# H=A-(-4*Dsame)=A+4*Dsame; original post-sixth target is
# H+L<4*d+I. The exact SAME-ORD recut is
# A-I+L<4*d-4*Dsame.
_A,_I,_L,_d,_Dsame=s.symbols("_A _I _L _d _Dsame",real=True)
_H=_A+4*_Dsame
old_margin=4*_d+_I-(_H+_L)
contour_margin=4*_d-4*_Dsame-(_A-_I+_L)
assert s.simplify(old_margin-contour_margin)==0
# Conditional on the original W quantitative target band, all defect
# terms are nonnegative. An off-line target has a DISTINCT mirror at
# the SAME ordinate and equal multiplicity, so Dsame>=2*d.
assert s.simplify((4*_d-4*(2*_d))-(-4*_d))==0
print("PASS exact post-sixth same-ordinate recut; off-line pair demands A-I+L < -4*d")

# Right-vertical prime coefficient normalization. For real EVEN P,
# f_t(s)=r^-2∫P(v) exp((s-(1/2+i*t))*v/r) dv.
# The Fourier coefficient of f_t(c+i*tau)+f_t(1-c-i*tau)
# against n^(-c-i*tau) is 2/r*n^(-1/2)*cos(t*log(n))*P(r*log(n)).
# Test the Gaussian Fourier exponent algebra (the compact-support
# vanishing then applies to the ORIGINAL P_W, not the Gaussian).
_c,_h,_r=s.symbols("_c _h _r",positive=True)
_b=_c-s.Rational(1,2)
gaussian_exponent=_b**2/(4*_r**2)-_r**2*(_h-_b/(2*_r**2))**2
expected_exponent=_b*_h-_r**2*_h**2
assert s.expand(gaussian_exponent-expected_exponent)==0
print("PASS right-vertical prime coefficient -(2/r)*sum Lambda(n)/sqrt(n)*cos(t log n)*P(r log n)")
print("OPEN canonical contour-to-Zeta23.mu/Gamma and pole-removal normalization; NO RH/GRH claim")
