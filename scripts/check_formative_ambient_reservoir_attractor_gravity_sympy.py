#!/usr/bin/env python3
"""Exact attractor/access/force versus power preflight, not a physical device simulation.

Original mathematical illustration inspired by existing Levin, Filsinger, and
antigravity Agda source owners. No measured control input, no claimed gain.
"""
from sympy import symbols, Rational as Q, sqrt, diff, simplify, factor, discriminant, Eq, solve
x,a,t,m,g,z,dz,da,G,R,Voc = symbols('x a t m g z dz da G R Voc', real=True)
checks=[]
def check(s,v):
    assert v is True or bool(v), f'{s}: {v}'
    checks.append(s)

# 1. Same energy functional, with multiple basins and a controllable tilt.
U=(x*x-1)**2/4-a*x
fx=-diff(U,x)
check('gradient field', simplify(fx-(x-x**3+a))==0)
check('unforced equilibria', simplify(fx.subs(a,0)-(x-x**3))==0)
check('left stable fixed point',fx.subs({a:0,x:-1})==0 and diff(U,x,2).subs({a:0,x:-1})>0)
check('right stable fixed point',fx.subs({a:0,x:1})==0 and diff(U,x,2).subs({a:0,x:1})>0)
check('zero unstable separator',fx.subs({a:0,x:0})==0 and diff(U,x,2).subs({a:0,x:0})<0)
check('barrier height at zero', simplify(U.subs({a:0,x:0})-U.subs({a:0,x:-1}))==Q(1,4))
check('left test point flows left unforced',fx.subs({a:0,x:Q(-1,2)})<0)
check('same test point flows right under tilt',fx.subs({a:Q(1,2),x:Q(-1,2)})>0)
check('parameter 1/2 removes left well',Q(1,2)>2/(3*sqrt(3)))
check('tilt cubic has single real root',discriminant(x**3-x-Q(1,2),x)<0)
check('after returning control to zero, positive point flows to positive basin',fx.subs({a:0,x:Q(1,2)})>0)
check('fixed-control gradient dissipation',simplify(diff(U,x)*fx+diff(U,x)**2)==0)
check('time-varying control has distinct parameter-work term',simplify(diff(U,x)*fx+diff(U,a)*da+diff(U,x)**2+x*da)==0)

# 2. A natural source at Voc=R=1, control changes load coupling, not available source.
P=lambda C: Voc**2*C/(1+R*C)**2
p_low=simplify(P(Q(1,8)).subs({Voc:1,R:1}))
p_match=simplify(P(Q(1)).subs({Voc:1,R:1}))
check('weak natural source coupling P=8/81',p_low==Q(8,81))
check('matched source coupling P=1/4',p_match==Q(1,4))
check('source-connected coupling raises load power 81/32 fold',p_match/p_low==Q(81,32))
check('source-connected coupling raises load power by 49/324',p_match-p_low==Q(49,324))
check('matched source power stationary derivative',simplify(diff(P(G),G).subs({G:1,R:1,Voc:1}))==0)
check('matched source power cannot exceed source ceiling in positive G model',simplify(Voc**2/(4*R)-P(G)-Voc**2*(R*G-1)**2/(4*R*(1+R*G)**2))==0)

# 3. Static force can be nonzero while mechanical POWER at rest is zero.
U_g=m*g*z
force=-diff(U_g,z)
check('stationary gravitational force nonzero symbolic',force==-m*g)
check('stationary mechanical power zero even with force',simplify(force*dz).subs(dz,0)==0)
check('moving a height delta h changes potential',simplify(U_g.subs(z,z+symbols('h'))-U_g)==m*g*symbols('h'))
print(f'{len(checks)}/{len(checks)} exact symbolic attractor, source-access, force/power checks PASS')
