#!/usr/bin/env python3
"""Explicit R=10^-10 original 4-window J2 branch and high-pole q4 margin.

Source: Lean RiemannQuantitativeScaledBump / FourWindow / PoleSameObject /
SignedPoleJointHorizontalJet. Uses Mathlib ContDiffBump.neg/le_one and inner
plateau, not Gaussian surrogate. SymPy checks exact source cancellations and
rational interval majorants. Analytic majorant arguments are recorded in the
companion ledger, not kernel-checked here. No actual-zeta-zero theorem.
"""
import sympy as s
F=s.Rational
lam,mu,e=s.symbols("lam mu e",real=True)
cs=(s.Integer(0),s.pi/3,s.pi/2,s.pi)
weights=(s.Integer(1),-s.Integer(1),lam,mu)
cf=lambda k:s.expand(sum(w*s.cos(k*c) for w,c in zip(weights,cs)))
sf=lambda k:s.expand(sum(w*c*s.sin(k*c) for w,c in zip(weights,cs)))
c2f=lambda k:s.expand(sum(w*c*c*s.cos(k*c) for w,c in zip(weights,cs)))
# Even normalized fixed-shape bump Y=R Z; e=E[Y²]/2.
# Fourier 2nd-order surrogates phi=1-e*k², phi'=-2e*k, phi''=-2e.
def A(k):return s.expand((1-e*k*k)*cf(k))
def M(k):return s.expand((1-e*k*k)*c2f(k)+2*e*cf(k)-4*e*k*sf(k))
A1,A2=A(1),A(2)
J=s.expand(A1*M(2)-A2*M(1))
mu0=(13*lam-8)/(144-54*lam)
assert s.simplify(J.subs({e:0,mu:mu0}))==0
assert s.simplify(s.diff(J,mu).subs(e,0)-s.pi**2*(8-3*lam)/4)==0
mu1=s.factor((-s.diff(J,e)/s.diff(J,mu)).subs({e:0,mu:mu0}))
half,two=F(1,2),F(2,3)
assert s.simplify(mu1.subs(lam,half)+4*(77+2*s.sqrt(3))/(507*s.pi))==0
assert s.simplify(mu1.subs(lam,two)+16*(34+3*s.sqrt(3))/(729*s.pi))==0
assert all(abs(float(mu1.subs(lam,l)))<1 for l in (half,two))
def trial(expr,l):
    m0=mu0.subs(lam,l);m1=mu1.subs(lam,l)
    return s.Poly(s.expand(expr.subs(lam,l).subs(mu,m0+m1*e)),e)
for l in (half,two):
    jj=trial(J,l)
    assert jj.nth(0)==0 and s.simplify(jj.nth(1))==0
# Original high-pole P and signed normalized profile Q at q=4.
B1,B2=(A(15)+A(17))/2,(A(14)+A(18))/2
P=s.expand(B1*A2-B2*A1)
Q=s.expand(2*(A1*(A(2)+A(6))-A2*(A(3)+A(5))))
pH,pT=trial(P,half),trial(P,two)
qH,qT=trial(Q,half),trial(Q,two)
K=s.Poly(s.expand(pT.as_expr()*qH.as_expr()
                   -pH.as_expr()*qT.as_expr()),e)
assert K.nth(0)==0 and s.simplify(K.nth(1)-F(120,13))==0

# Rigorous envelopes for nonnegative even |Y|<=R with R<=1/100:
# |phi-(1-e k²)|<=k⁴R⁴/24,
# |phi'+2ek|<=k³R⁴/6, |phi''+2e|<=k²R⁴/2.
# |weights| sum <3, |c|<4, |A1,A2|<=3, |M1,M2|<=75.
assert 1+1+F(2,3)+F(1,10)<3
assert F(18**2,20000)<1 # all truncated Fourier values abs<=1
# J true minus truncated at same mu trial:
# |A-Atr|<=2R4, |M-Mtr|<=70R4,
# |J-Jtr|<=2*(2*75+3*70)R4=720R4.
assert 2*(2*75+3*70)==720
# Jtr coefficient l1 bound via ||A||<=20, ||M||<=456:
assert 3+(3*4+1)+4==20
assert 48+(3*(16*4+2+4*4*2)+16)+(16*4+2+4*4*2)==456
assert 2*20*456==18240
# Since first two coeff vanish, |Jtrial|<= (720+18240/4)R4
assert 720+F(18240,4)==5280
# Atomic dJ/dmu >=3*pi²/2>13.5. For R<=.01 deviation
# <=1188R², hence true dJ/dmu>10 for all |mu|<=.1.
assert 3*F(3)**2/2-F(1188,10000)>10
assert mu0.subs(lam,half)==-F(1,78)
assert mu0.subs(lam,two)==F(1,162)
assert F(1,78)+F(1,20000)+F(600,100**4)<F(1,10)
# IVT brackets mu_trial +/-600R4 (10*600>5280); unique
# J2 root in this interval, |mu_exact-mu_trial|<=600R4.
assert 10*600>5280

# Fourier-value errors: k<=2: Aerr<=2R4; k<=6 <=162R4;
# k<=18 <=13122R4. At both source endpoints:
Perr=2*(13122*3+3*2)
Qerr=2*(2*(162*6+3*(162+162)))
assert Perr==78744 and Qerr==7776
# |P|<=18, |Q|<=72; two-term selected determinant error.
K_input=2*(Perr*72+18*Qerr)
assert K_input==11619072
# |dP/dmu|<=12, |dQ/dmu|<=48: both roots differ <=600R4.
K_branch=2*(18*48+12*72)*600
assert K_branch==2073600
# Coefficient-l1 norm of all trial A(k) at frequencies <=18 <=1300.
# P polynomial norm <=2*1300², Q <=8*1300²,
# selected K norm <=2*(2*1300²)*(8*1300²).
Acoef=3+(3*18**2+1)+18**2
assert Acoef==1300
Kcoef=2*(2*Acoef**2)*(8*Acoef**2)
assert Kcoef==91395200000000
C=Kcoef//4+K_input+K_branch
assert C==22848813692672 and C<23000000000000
# Real source: 0<=unitBump<=1, unitBump=1 on [-1/2,1/2],
# support in [-1,1]. Normalized m2=E[Z²]>= (1/12)/2=1/24.
# Therefore e>=R²/48 and positive K term >=(5/26)R².
assert F(1,12)/2==F(1,24)
assert F(120,13)/48==F(5,26)
R=F(1,10**10)
assert F(5,26)-C*R**2>F(1,6)
# Hence exact near-atomic J2-selected high-pole K_inf(0,4)>R²/6.
# Separate finite-t source bound |K_t(a,4)-K_inf(0,4)|<=13e6/t²
# for all |a|<=1/2,t>=200. At t>=10^14:
T=10**14
assert R**2/6-F(13000000,T**2)==F(11,300)*R**2>0

# Exact selected J4 sign on both branches:
# |(x^4 cos(kx))''|<=4800 for |x|<5,k=1,2.
assert 12*25+8*2*125+4*625==4800
# |N_k-Nk_atom|<=7200R²; |N_k|<=1875; |Ak-Ak_atom|<=6R²,
# hence |J4_smooth(mu)-J4_atom(mu)|<=65700R².
J4smooth=2*(6*1875+3*7200)
assert J4smooth==65700
# Original dJ4_atom/dmu =pi^4*(32-15lambda)/16<392,
# |mu_exact-mu0|<=e+600R4<=.56R² for R<=.01.
assert 4**4*F(49,32)==392
assert F(1,2)+F(600,10000)<=F(56,100)
assert J4smooth+392*F(56,100)<67000
# Atomic J4(mu0) <=-pi^4/243<-1/3. Thus J4<-1/4 at chosen R.
assert 67000*R**2<F(1,12)

# Negative control: same high-pole atomic source q=1 is negative.
Q1=s.expand(2*(A1*(A(1)+A(3))-A2*(A(0)+A(2))))
qH1,qT1=trial(Q1,half),trial(Q1,two)
assert s.simplify(pT.nth(0)*qH1.nth(0)-pH.nth(0)*qT1.nth(0)
                  +F(80,351))==0
print("PASS original J2 roots: |mu-mutrial|<=600R4, both mu within corridor")
print("PASS original J4 endpoints strictly less than -1/4")
print("PASS R=10^-10: K_inf(0,4)>R²/6")
print("PASS t>=10^14, |a|<=1/2: K_t(a,4)>11R²/300")
print("PASS negative q1 atomic control -80/351; no all-q promotion")
print("C high-pole R4 majorant =",C)
print("OPEN: Lean kernel receipt, actual-zero signed sum, prime-side/slack")
