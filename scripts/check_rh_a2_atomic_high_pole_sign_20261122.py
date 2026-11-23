#!/usr/bin/env python3
"""RH P0 A2: exact leading local scalar sign for original atomic high-pole witness.

Original Lean owner:
  Synthesis/RiemannProjectiveQuarticFourWindowSignedPoleA2ScalarAudit.lean
  Synthesis/RiemannProjectiveQuarticFourWindowSignedPolePostSixthAbsorb.lean
  Synthesis/RiemannProjectiveQuarticFourWindowSignedPolePair.lean
  Synthesis/RiemannProjectiveQuarticFourWindowSignedPoleV4EndpointAbsorb.lean
Checks are algebraic and exact rational. The actual A2 theorem involves a
smooth R>0 finite-t W, actual zeros, signed FarExact and compensation threshold;
none is inferred from the atomic calculation.
"""
import sympy as s

pi=s.pi
c=(s.Integer(0),pi/3,pi/2,pi)
half=s.Rational(1,2)
two=s.Rational(2,3)
def original_endpoint(l):
    mu=(13*l-8)/(144-54*l)
    weights=(s.Integer(1),s.Integer(-1),l,mu)
    a1=s.factor(sum(w*s.cos(ci) for w,ci in zip(weights,c)))
    a2=s.factor(sum(w*s.cos(2*ci) for w,ci in zip(weights,c)))
    b1=s.factor(sum(w*s.cos(16*ci)*s.cos(ci) for w,ci in zip(weights,c)))
    b2=s.factor(sum(w*s.cos(16*ci)*s.cos(2*ci) for w,ci in zip(weights,c)))
    pole=s.factor(b1*a2-b2*a1)
    # Original signed normalized profile: 4G(x)*(A1*cos2x-A2*cosx).
    mass=[s.factor(4*w*(a1*s.cos(2*ci)-a2*s.cos(ci)))
          for w,ci in zip(weights,c)]
    return pole,mass
pole_h,profile_h=original_endpoint(half)
pole_t,profile_t=original_endpoint(two)
assert pole_h==s.Rational(9,8) and pole_t==1
masses=[s.factor(pole_t*h-pole_h*t)
        for h,t in zip(profile_h,profile_t)]
assert masses==[-s.Rational(40,117),0,s.Rational(160,351),
                -s.Rational(40,351)]
# Original strength is minus one-fourth the signed profile's fourth moment.
S=s.factor(-sum(w*ci**4 for w,ci in zip(masses,c))/4)
M6=s.factor(sum(w*ci**6 for w,ci in zip(masses,c)))
# G1 fourth-Lipschitz cosh-majorant: ∫|P(x)| cosh|x| |x|^5 dx.
L=s.simplify(sum(abs(w)*s.cosh(ci)*ci**5
                 for w,ci in zip(masses,c)))
assert S==5*pi**4/234
assert M6==-25*pi**6/234
assert s.simplify(L-5*pi**5*(s.cosh(pi/2)+8*s.cosh(pi))/351)==0
# Selected M6 cap and strength-floor conditions hold in the atomic limit.
assert s.Rational(25,234)<s.Rational(3,20)
assert s.Rational(5,234)>s.Rational(7,1600)

eta=1/(pi+1)
# Let v=t/16, ell=log(t)/(2*pi). RvM N(t-r-1,t+r) has
# leading 2r*ell with r=eta*v.
# EV=O(log t), so EV/v^6=O(log t/t^2);
# r^2*N/v^6=O(log t/t^3).
# The local A2 leading coefficient in eta^5*ell/v is
C=s.simplify(-S/15+pi**6*eta**2/2400+L*eta**2/8500)
# A2 leading sign is strictly negative by rational enclosures:
# 3<pi<22/7 implies eta^2<1/16; 0<cosh(pi/2),cosh(pi)<cosh4<28.
# cosh4<28 follows from exp4<55 and exp(-4)<1.
p_hi=s.Rational(22,7)
e4_series=sum(s.Rational(4**n,s.factorial(n)) for n in range(21))
e4_tail=s.Rational(4**21,s.factorial(21))/(1-s.Rational(4,22))
assert e4_series+e4_tail<55  # exact rational geometric tail
L_hi=5*p_hi**5*9*28/351
S_lo=5*s.Integer(3)**4/234
C_hi=-S_lo/15+p_hi**6/(2400*16)+L_hi/(8500*16)
assert C_hi<-s.Rational(1,20)
# Equivalent exact strength/L threshold for a negative leading local coefficient.
assert s.simplify(C+(
    S-(pi**6*eta**2/160+3*eta**2*L/1700)
)/15)==0
# Source's existing absolute shell bound at the cutoff J=floor(t/2000)
# retains a positive 72*A/sqrt(J). Since J<=t/2000, for A>=1
# the MAJORANT (not the signed FarExact itself) is >=72*sqrt(2000/t).
# This O(t^-1/2) resolution is too coarse to infer cancellations
# on a local O(log(t)/t) scale without further information.
print("PASS original atomic high-pole selected centre weights",masses)
print("PASS S=5*pi^4/234; M6=-25*pi^6/234; explicit L")
print("PASS atomic strength floor and signed M6 cap")
print("PASS exact A2 leading local coefficient C < -1/20")
print("PASS exact strength-L threshold; no decimal-only sign argument")
print("S_at =",s.N(S,14),"L_at =",s.N(L,14),"C_at =",s.N(C,14))
print("OPEN: smooth finite-t selected witness uniform ratio S/L")
print("OPEN: exact signed far-minus-compensation, actual zeros, RH G3")
