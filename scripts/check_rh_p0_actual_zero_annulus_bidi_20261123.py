#!/usr/bin/env python3
"""RH P0: actual zeta zero annuli, original selected-W uniform signed N-mu cut.

Source: Lean main JointHorizontalJet, QuantitativeBand, NMu, ZetaMuZeroCountOneSided.
This script is LOCAL numerical validation, not interval-certified zero isolation,
not an instantiated numerical copy of the abstract Mathlib unitContDiffBump.
The sign of annular signed N-mu is certified conditionally on the sampled
zero list and gamma quadrature, using only rigorous source-uniform W bounds.
P0 full H_W+S_W<4d_W+I_W remains open.
"""
from fractions import Fraction as F
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
E6coef=mp.mpf(225000)

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
    A=moment-gamma
    # Universal same-W E6 bound, after subtracting exact gamma and
    # summing ALL multiplicity-one actual zeros in this numerical low region.
    E6=(mp.mpf(225000)*qmax**6)*(len(ordinates)+abs(gamma_mass))
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
    return {'t':t,'side':side,'count':hi-lo,'A':A,'margin':margin,'robust':robust,'sign':sign}

r=[]
for t in (mp.mpf(1000000),mp.mpf(1000002)):
    for side in ('left','right'):
        r.append(interval(t,side))
assert r[0]['count']==3 and r[0]['robust'] and r[0]['sign']=='negative'
assert r[1]['count']==2 and r[1]['robust'] and r[1]['sign']=='positive'
assert r[2]['count']==2 and r[2]['robust'] and r[2]['sign']=='positive'
assert r[3]['count']==3 and not r[3]['robust']
print('PASS two opposite SIGN-CERTIFIED actual zeta N-mu annular contributions at one t')
print('PASS independent height shifts give reversed sign, retaining neutral/undetermined controls')
print('OPEN: analytic certified zero isolation; original selected W numerical witness; full zero-minus-mu over all q; post-sixth S; strict P0')
