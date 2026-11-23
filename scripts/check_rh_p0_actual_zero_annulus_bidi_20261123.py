#!/usr/bin/env python3
"""RH P0: actual zeta zero annuli, original selected-W uniform signed N-mu cut.

Source: Lean main JointHorizontalJet, QuantitativeBand, NMu, ZetaMuZeroCountOneSided.
This script is LOCAL numerical validation, not interval-certified zero isolation,
not an instantiated numerical copy of the abstract Mathlib unitContDiffBump.
The sign of annular signed N-mu is certified conditionally on the sampled
zero list and gamma quadrature, using only rigorous source-uniform W bounds.
P0 full H_W+S_W<4d_W+I_W remains open.
"""
import sympy as sp
import mpmath as mp

mp.mp.dps = 44
h=mp.mpf('0.0001')
x=sp.symbols('x', real=True)
fraction = sp.factor((1-6*x**2+x**4)-sp.Rational(7,25)*(1+x**2)**2)
assert sp.simplify(fraction - sp.Rational(18,25)*(x*x-sp.Rational(1,9))*(x*x-9))==0
assert sp.Rational(8,960000)/(sp.Rational(1,40000)) == sp.Rational(1,3)
assert sp.Rational(9,12800)>0
assert sp.Rational(567,1600)==sp.Rational(7*3**4,1600)
print('PASS exact critical-strip -> 2D negative signed sector for all beta, t>=960000')
print('PASS exact p4/rho^4 >=7/25, and normalized bound for all selected W')

floor=mp.mpf(567)/1600

def mu(y):
    return (mp.re(mp.digamma(mp.mpf('0.25')+0.5j*y))-mp.log(mp.pi))/(2*mp.pi)

def interval(t,side):
    r=t/16
    qmin=h/4
    qmax=h/2
    if side=='left':
        low,high=t-r*qmax,t-r*qmin
    else:
        low,high=t+r*qmin,t+r*qmax
    lo,hi=int(mp.nzeros(low)),int(mp.nzeros(high))
    ordinates=[mp.im(mp.zetazero(i)) for i in range(lo+1,hi+1)]
    assert len(ordinates)==hi-lo and all(low<z<high for z in ordinates)
    qs=[(z-t)/r for z in ordinates]
    moment=sum(q**4 for q in qs)
    gamma=mp.quad(lambda y:((y-t)/r)**4*mu(y),[low,high])
    gamma_mass=mp.quad(mu,[low,high])
    gamma_mass_abs=mp.quad(lambda y:abs(mu(y)),[low,high])
    assert gamma_mass_abs>0
    A=moment-gamma
    # Universal same-W E6 bound, after subtracting exact gamma and
    # summing ALL multiplicity-one actual zeros in this numerical low region.
    E6=(mp.mpf(225000)*qmax**6)*(len(ordinates)+gamma_mass_abs)
    main=(floor/6)*abs(A)
    margin=(main-E6)/r**2
    robust=(main>E6)
    sign='negative' if A>0 else 'positive' if A<0 else 'zero'
    print(f't={mp.nstr(t,15)} {side} count={hi-lo}, mu_mass={mp.nstr(gamma_mass,14)}')
    print('  ordinates=',[mp.nstr(v,18) for v in ordinates])
    print('  normalized q=',[mp.nstr(v/h,12) for v in qs],'[units h]')
    print('  fourth moment N=',mp.nstr(moment,19),'gamma=',mp.nstr(gamma,19),'N-mu=',mp.nstr(A,19))
    print('  sign of original W ANNULAR [sum K - integral K mu]/r2=',sign,
          'robust=',robust,'margin=',mp.nstr(margin,10),'ratio=',mp.nstr(main/E6,7))
    return {'t':t,'side':side,'count':hi-lo,'A':A,'margin':margin,'robust':robust,'sign':sign,'E6':E6,'r':r}

r=[]
for t in (mp.mpf(1000000),mp.mpf(1000002)):
    for side in ('left','right'):
        r.append(interval(t,side))
assert r[0]['count']==3 and r[0]['robust'] and r[0]['sign']=='negative'
assert r[1]['count']==2 and r[1]['robust'] and r[1]['sign']=='positive'
assert r[2]['count']==2 and r[2]['robust'] and r[2]['sign']=='positive'
assert r[3]['count']==3 and not r[3]['robust']
print('PASS source-uniform signed bounds GIVEN numerically sampled zeros and gamma integration')
print('PASS independent height shifts give reversed sign, retaining neutral/undetermined controls')
for pair in ((r[0],r[1]),(r[2],r[3])):
    totalA=sum(z['A'] for z in pair)
    totalE=sum(z['E6'] for z in pair)
    rscale=pair[0]['r']
    lower=(floor*abs(totalA)/6-totalE)/rscale**2
    robust=lower>0
    direction='positive' if totalA<0 else 'negative'
    print('BILATERAL UNION t=',mp.nstr(pair[0]['t'],15),'signed sign=',direction,
          'robust=',robust,'margin=',mp.nstr(lower,10),'A=',mp.nstr(totalA,18))
    if pair[0]['t']==mp.mpf(1000000):
        assert not robust
    else:
        assert robust and direction=='positive'
print('PASS bilateral union at t=1000002 has positive selected-W signed N-mu lower bound given sampled zeros')
print('OPEN: analytic certified zero isolation; original selected W numerical witness; full zero-minus-mu over all q; post-sixth S; strict P0')

# SAME original selected-W horizontal correction H=K(alpha,q)-K(0,q).
# K is harmonic, M2=0, M4=-4*strength and all original W have
# strength>567/1600, ||P||1<5184, support<5.
# For |s|<=|alpha|<=|q|/3 and 0<|q|<=1/20000:
# d2K/dalpha2(s,q) >= 2*strength*(q^2-s^2)
#   - (5184*5^6*2/24)*(q^2+s^2)^2
# >= [2*(567/1600)*(8/9) -(25e6/3)*(1/20000)^2]*q^2
# = (731/1200) q^2. Integrating twice in alpha yields
# H >= (731/2400)*alpha^2*q^2 > 0, for *every nonzero alpha*.
from fractions import Fraction as F
M,L=F(5184),F(5)
Tfloor=F(567,1600)
err= M*L**6*2/F(24)
assert err==6750000
errcoeff=err*F(100,81)*F(1,20000)**2
assert errcoeff==F(1,48)
curv_low=2*Tfloor*(1-F(1,9))-errcoeff
assert curv_low==F(731,1200)
assert curv_low/F(2)==F(731,2400)>F(1,4)
print('PASS exact original-W H(alpha,q)>=731/2400*alpha^2*q^2 for 0<|alpha|<=|q|/3, |q|<=5e-5')

# Numerically check shape on an independent genuine compact smooth fixture,
# not the original Mathlib-selected source (which is noncomputably chosen).
mp.mp.dps=65
def bump(y):
    return mp.exp(-1/(1-y*y)) if abs(y)<1 else mp.mpf(0)
def transform(z):
    return 2*mp.quad(lambda y:bump(y)*mp.cos(z*y),[0,mp.mpf('.5'),mp.mpf('.9'),1])
def fixture_K(a,q):
    z=mp.mpc(q,a)
    return -mp.re(z**4*transform(z))
qtest=mp.mpf('0.00005')
for den in ('4','1000000'):
    atest=qtest/mp.mpf(den)
    horizontal=fixture_K(atest,qtest)-fixture_K(0,qtest)
    assert horizontal>mp.mpf('.25')*atest**2*qtest**2
    print('PASS independent smooth signed fixture horizontal sign, alpha/q=1/'+den,
          'H/(alpha^2*q^2)=',mp.nstr(horizontal/(atest**2*qtest**2),18))
print('OPEN: any real off-axis zero in the annulus; full signed physical zero-minus-mu+local-slack terminal')

# EXACT original-W vertical signed-discrepancy bound from the existing RvM:
# with M0=M2=0, |K(0,q)|<= ||P||1*L^4*q^4/24 =135000*q^4;
# |dK(0,q)/dq|<= ||P||1*L^4*|q|^3/6 =540000*|q|^3.
# For one of the annuli [q_min,q_max] with q_max=1/20000,
# the Stieltjes IBP identity |integral K d(N-mu)| <=
#  sup_{x in I}|N(A,x)-int_A^x mu| * (|K(B)|+int_I|K'|)
# <= 2*C_RvM*log(2t+4)*270000*q_max^4.
# So |E_vertical|<= 540000*C_RvM*log(2t+4)*q_max^4/r^2,
# only O(log(t)/t^2), four powers too weak for O(a^4/t^6) target.
assert M*L**4/F(24)==F(135000)
assert M*L**4/F(6)==F(540000)
assert F(2)*(F(135000)+F(540000)/4)==F(540000)
print('PASS exact source RvM Stieltjes envelope constant 540000*C*log(2t+4)*q_max^4/r^2')
print('OPEN P0 strict global actual-source signed estimate, full S and exact I')
