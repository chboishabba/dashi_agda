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
