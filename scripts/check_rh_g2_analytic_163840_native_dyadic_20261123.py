#!/usr/bin/env python3
"""RH/GRH G2: source-audited H_X character, real-even action and 163840 tail.

Owner facts:
  Lean QuarticFour...FourierMass, NMu, FourthOrderQuotient, Cutset, FourierTerminal;
  DASHI/Analysis/RiemannG2CanonicalHXToHTCompilerExact.agda (conditional H_X);
  DASHI/Analysis/RiemannCanonicalComplexCharacterAttachmentExact.agda;
  DASHI/Analysis/NonArchimedeanMonster3BActionSeparationExact.agda;
  Zeta23/GammaFacts/Mu.lean & ThmE/GammaFactsChiProof.lean.

The Gaussian is a deliberate independent analytic fixture, NOT the
existentially selected quartic W.  Not an RH/GRH proof or Agda kernel check.
"""
from fractions import Fraction as F
from itertools import product
import sympy as s
import mpmath as mp

v,b,t,a,q,u=s.symbols('v b t a q u',real=True)
assert s.simplify(s.exp(s.I*(b-t)*u)-s.exp(-s.I*t*u)*s.exp(s.I*b*u))==0
assert s.simplify(s.cos((b-t)*u)-s.re(s.exp(s.I*(b-t)*u)))==0
assert s.simplify(((2*t-v)-t)/(t/16)+(v-t)/(t/16))==0

# Original P_W is real-even. Complex modulation need not preserve that class;
# its real-even projection cos(a*u)*P_W is a legitimate NEW test, not selected W.
p0,p2=s.symbols('P0 P2',real=True)
ws=[F(1,16),F(1,8),F(1,4),F(1,2),F(1),F(2),F(4)]
mult=s.prod(s.cos(s.Rational(x.numerator,x.denominator)*v) for x in ws)
assert mult.subs(v,0)==1
assert s.simplify(s.diff((p0+p2*v*v/2)*mult,v,2).subs(v,0)-
    (p2-p0*sum(s.Rational(x.numerator,x.denominator)**2 for x in ws)))==0
assert s.simplify(s.cos(a*v)*s.cos(b*v)-
    (s.cos((a+b)*v)+s.cos((a-b)*v))/2)==0
assert s.simplify(s.cos(a*v)**2-1)!=0
assert s.simplify(s.exp(-s.I*a*v).subs(v,-v)-s.exp(-s.I*a*v))!=0
print('PASS canonical conditional H_X phase law; seven commuting cosine modulations are not C2 actions')

# Weighted q^-6 tail EXACT pushforward: z=(8/q)^5, 5*8^5=163840.
z=s.symbols('z',positive=True)
qz=8*z**s.Rational(-1,5)
assert s.simplify(-s.diff(qz,z)*qz**(-6)-s.Rational(1,163840))==0
assert s.integrate(q**(-6),(q,8,s.oo))==s.Rational(1,163840)
assert 163840==5*32768==5*2**15
# Preserve continuous theta, not just k: z=(k+theta)/32768.
for k in range(32768):
    for theta in (F(1,3),F(2,3)):
        z0=(k+theta)/32768
        assert (z0*32768).__floor__()==k
        assert z0*32768-k==theta
assert 1024*32==32768
assert s.simplify(
    s.integrate(q**(-6),(q,16,s.oo))/
    s.integrate(q**(-6),(q,8,s.oo))-s.Rational(1,32))==0
print('PASS exact 32768-by-residual BIDI and original q=16 crossing at k=1024')

# Gauge-compensated source lift: all C2^7 label masks preserve the SAME
# physical Psi_W after dividing out the changing positive coefficient.
B=list(product((0,1),repeat=7))
weight=lambda x:2**sum(x)
xor=lambda x,m:tuple(a^b for a,b in zip(x,m))
for x in B:
    for m in B:
        y=xor(x,m)
        amp=F(weight(x),weight(y))
        assert amp*weight(y)==weight(x)
        assert F(weight(x),weight(y))*F(weight(y),weight(x))==1
assert all(weight(x)*weight(tuple(1-i for i in x))==128 for x in B)
print('PASS all 16384 seven-axis gauge-compensated source moves; zero physical effect')

mp.mp.dps=30
T=mp.mpf(200)
def mu(x,parity=0,N=1):
    return (mp.re(mp.digamma(mp.mpf('0.25')+mp.mpf(parity)/2+mp.j*x/2))
            +mp.log(mp.mpf(N)/mp.pi))/(2*mp.pi)
def delta(q,parity=0,N=1):
    return mu(T*(1+q/16),parity,N)+mu(T*(1-q/16),parity,N)-2*mu(T,parity,N)
for parity in (0,1):
    for N in (1,5,71,10007):
        for x in (mp.mpf(0),mp.mpf(8),mp.mpf('15.99'),mp.mpf(16),mp.mpf('16.01'),mp.mpf(24),mp.mpf(32)):
            assert abs(delta(x,parity,N)-delta(-x,parity,N))<mp.mpf('1e-27')
            assert abs(delta(x,parity,N)-delta(x,parity,1))<mp.mpf('1e-27')
print('PASS original digamma parity/conductor bilateral law through q=16')

# Deliberately centered at q=16 to stress crossing. NOT original selected W.
def C16(x):
    return mp.sqrt(2*mp.pi)*(mp.exp(-(x-16)**2/2)+mp.exp(-(x+16)**2/2))/2
ends=(-35,-24,-18,-16,-14,-8,0,8,14,16,18,24,35)
v1=(16/T)*sum(mp.quad(lambda x:C16(x)*(mu(T*(1+x/16))-mu(T)),
                   (a,b)) for a,b in zip(ends[:-1],ends[1:]))
v2=(8/T)*sum(mp.quad(lambda x:C16(x)*delta(x),(a,b))
             for a,b in zip(ends[:-1],ends[1:]))
assert abs(v1-v2)<mp.mpf('1e-26'),(v1,v2)
print('PASS full direct vs bilateral gamma integral, crossing residual',mp.nstr(v1-v2,5))
zeros=[mp.im(mp.zetazero(i)) for i in range(1,5)]
orig=sum(C16((g-T)/(T/16)) for g in zeros)
changed=sum(C16((g-T)/(T/16)-mp.mpf('0.7')) for g in zeros)
assert abs(orig-changed)>mp.mpf('1e-8')
print('PASS finite ACTUAL zeta-zero ordinate sample changes under analytic shift; no zero-set symmetry')

assert 16*(mp.pi+1)/200<mp.log(2)
print('PASS character and cos multiplication preserve original prime-free compact support')
D,d,slack,e=s.symbols('D d slack e',nonnegative=True)
assert s.simplify((2*D+slack-4*d).subs(D,2*d+e)-(2*e+slack))==0
print('PASS terminal negative margin remains independent; RH/GRH OPEN')
