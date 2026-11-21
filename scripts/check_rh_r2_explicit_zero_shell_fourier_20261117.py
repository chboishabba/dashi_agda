#!/usr/bin/env python3
"""R2 unconditional explicit zero shell A=160, conditional smooth-kernel C.

This checker verifies symbolic arithmetic and conservative real-inequality
reduction. It does NOT prove the cited zero-count theorem or selected-W norms.
"""
from math import comb
import sympy as s
k,t,n,x,r,L,a=s.symbols("k t n x r L a",nonnegative=True)
m=s.symbols("M0:5",nonnegative=True)
N=s.symbols("N",positive=True)
# Published Bellotti--Wong (2025): for U>=e,
# |N(U)-U/(2*pi)log(U/(2*pi*e))|
# <=0.10076 log(U)+0.24460 log log(U)+8.08344.
# Since loglog(U)<=log(U) and U log U>=e for U>=e:
# N(U) <= (1+0.34536+8.08344/e)*U log U <5 U log U.
assert 1+s.Rational(10076,100000)+s.Rational(24460,100000)+s.Rational(808344,100000)/s.E <5
# For U<e use monotonic N(U)<=N(e) <= 5e <20.
assert s.N(5*s.E)<20
# Therefore N(U) <=20(1+U)log(e+U), all U>=0.
# Every two-sided unit shell is bounded by 2 N(t+k+1), including multiplicities.
# For X=1+t+k >=2:
# 2*20*(1+t+k+1)*log(e+t+k+1)
# <=160*(1+t+k)*log(e+t+k).
X=s.symbols("X",positive=True)
assert s.expand(2*40*X-40*(X+1))==40*(X-1)
assert s.limit(s.log(s.E+X+1)/s.log(s.E+X),X,s.oo)==1
# Log inequality log(e+X+1)<=2log(e+X) for X>=1,
# since (e+X)^2 >= e+X+1. Prove polynomial difference positive:
assert s.expand((s.E+X)**2-(s.E+X+1)) == X**2+X*(2*s.E-1)+s.E**2-s.E-1
assert s.N(s.E**2-s.E-1)>0

# Fourier family F(alpha,q)=integral P(u)exp(alpha*u)exp(i*q*u)du
# supp P subset [-L,L], |alpha|<=a:
# |F| <= exp(aL) sum_j binom(4,j)a^(4-j)||P^(j)||_1 / |q|^4.
D=s.expand(sum(comb(4,j)*a**(4-j)*m[j] for j in range(5)))
assert D==m[4]+4*a*m[3]+6*a*a*m[2]+4*a**3*m[1]+a**4*m[0]
# Source physical scaling is mult/r^2 * F(alpha,(gamma-t)/r);
# k<=|gamma-t|, k>=1 => |term|/mult <=
# 16*r^2*exp(aL)*D/(k+1)^4.
C=16*r*r*D
assert s.simplify(C/(16*r*r)-D)==0

# 22 Nov SOURCE CORRECTION: the selected W integral representation is
# ALREADY a theorem in the ORIGINAL Lean
# Synthesis/RiemannProjectiveQuarticFourWindowSignedPoleJointHorizontalJet:
#   W.signedNormalizedPairKernel_eq_combinedIntegral
#   W.signedLiteralPairSourceTerm_eq_normalizedPairKernel.
# No separate selected-W representation theorem is newly required.
#
# Full horizontal-weighted analytic test uses the same selected
# combined C^4 compact profile P_W, not its alpha=0 base alone:
#   P_alpha(u) = P_W(u)*cosh(alpha*u).
# The previously compiled source fourth-IBP theorem then has its
# exact Leibniz derivative envelope on |u|<=L and |alpha|<=a.
u,alpha=s.symbols("u alpha",real=True)
P=s.Function("P_W")(u)
product4=s.diff(P*s.cosh(alpha*u),u,4)
leibniz4=sum(
    comb(4,j)*alpha**(4-j)*s.diff(P,u,j)
    * (s.cosh(alpha*u) if (4-j)%2==0 else s.sinh(alpha*u))
    for j in range(5)
)
assert s.simplify(product4-leibniz4)==0
assert s.simplify(product4.subs(alpha,-alpha)-product4)==0
assert s.expand(leibniz4.subs(alpha,0)-s.diff(P,u,4))==0
# Q_W(alpha,q) even in the HORIZONTAL displacement, not necessarily
# nonnegative: this fact is already exact for the source cosh integral.
assert s.simplify(s.cosh(-alpha*u)-s.cosh(alpha*u))==0
# With r=t/16 and true zeta strip displacement |beta-1/2|<=1/2,
# the normalized horizontal parameter obeys |alpha|<=8/t;
# the complete literal term carries multiplicity/r^2.
tr=s.symbols("t_selected",positive=True)
rad=tr/16
amax=8/tr
assert s.simplify((s.Rational(1,2)/rad)-amax)==0
# A bound with unknown positive derivative norms M_j is valid, but
# numeric uniform-in-t constants and the signed infinite sum are OPEN.
weighted_profile_bound=s.exp(amax*L)*sum(comb(4,j)*amax**(4-j)*m[j] for j in range(5))
assert s.simplify(weighted_profile_bound.subs({L:0,m[0]:0,m[1]:0,m[2]:0,m[3]:0})-m[4])==0
assert s.simplify(rad**2*weighted_profile_bound/(rad**2)-weighted_profile_bound)==0
print("PASS: selected-W cosh-weighted full fourth derivative, 5 Leibniz terms")
print("PASS: both horizontal sides, alpha=0 base recovery, beta-strip scaling")
print("PAID ORIGINAL SOURCE: selected combined kernel and literal zero term identity")
print("OPEN: actual selected-W numeric derivative constants, t-uniform signed gap")

# The older tail-majorant used 4*A*C; retain its algebra.
f=(1+t+x)**2/(1+x)**4
I=s.integrate(f,(x,n,s.oo))
J=1/(n+1)+t/(n+1)**2+t*t/(3*(n+1)**3)
assert s.simplify(I-J)==0
assert s.simplify(s.diff(f,x)+2*(1+t+x)*(1+2*t+x)/(1+x)**5)==0
assert s.limit(f.subs(x,n)+I,n,s.oo)==0
print("PASS: unconditional shell constant A=160 arithmetic (using cited zero theorem)")
print("PASS: conditional fourth-derivative Fourier envelope and normalized rescaling")
print("C(t,W) = 16*(t/16)^2*exp(L*a)*(",D,")")
print("PASS: symbolic fixed-t cofinal O(1/n) bound")
print("NOT DONE: actual W derivative norm constants, complete horizontal physical tail uniformity, certified finite signed gap, uniform t/rho margin, native kernel")
