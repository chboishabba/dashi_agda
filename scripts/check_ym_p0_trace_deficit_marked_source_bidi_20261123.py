#!/usr/bin/env python3
"""Original 4D SU(N) global Wilson trace<->deficit affine source BIDI.

The theorem is algebraic for full positive continuous Haar SU(N). The exact
fixture is original 1536-plaquette 12-live-link Z2 subset, NOT full Haar.
"""
from fractions import Fraction as Q
from itertools import product
from collections import defaultdict
from pathlib import Path
from runpy import run_path
import sympy as S

x=run_path(str(Path(__file__).with_name('check_ym_p0_sun_original_two_mark_bad_event_20261123.py')))
records=x['original']
rtrace=Q(9,100)
rdef=Q(9,109)
checks=0

def check(v,msg=''):
    global checks
    assert v,msg
    checks+=1

def coeff(rows):
    return tuple(sum(w*f**i*g**j for w,f,g,bad in rows)
                 for i,j in ((0,0),(1,0),(0,1),(1,1)))

def deficit(a):
    a0,b,c,d=a
    return (a0,a0-b,a0-c,a0-b-c+d)

def kval(a,s,t):
    a0,b,c,d=a
    return a0+b*s+c*t+d*s*t

def hess(a,s,t):
    a0,b,c,d=a
    return Q(a0*d-b*c,1)/kval(a,s,t)**2

A,B,C,D,s,t=S.symbols('A B C D s t')
k=S.expand(A+s*B+t*C+s*t*D)
j=S.expand(A+s*(A-B)+t*(A-C)+s*t*(A-B-C+D))
sp=-s/(1+s);tp=-t/(1+t)
check(S.factor(j-(1+s)*(1+t)*k.subs({s:sp,t:tp},simultaneous=True))==0,'source chart')
check(S.expand(A*(A-B-C+D)-(A-B)*(A-C))==A*D-B*C,'determinant invariant')
check(S.simplify(S.diff(S.log(j),s,t) -
             S.diff(S.log(k),s,t).subs({s:sp,t:tp}, simultaneous=True)/((1+s)**2*(1+t)**2))==0,'mixed chart chain')
check(rdef/(1-rdef)==rtrace,'matched complex radius 9/109 -> 9/100')

fibres=defaultdict(list)
for bits,entry in enumerate(records):
    fibres[((bits>>0)&1,(bits>>8)&1)].append(entry)
subsets=[('full',records),('good',[v for v in records if not v[3]]),
         ('bad',[v for v in records if v[3]])]
for W,rows in sorted(fibres.items()):
    subsets.append(('coarse'+str(W),rows))
    for typ,sel in (('good',[v for v in rows if not v[3]]),('bad',[v for v in rows if v[3]])):
        if sel: subsets.append((typ+str(W),sel))

for name,rows in subsets:
    a=coeff(rows); b=deficit(a)
    check(a[0]>0,'strict source mass '+name)
    check(a[0]*a[3]-a[1]*a[2] == b[0]*b[3]-b[1]*b[2], 'determinant source '+name)
    for u,v in product((-rdef,-Q(1,20),Q(0),Q(1,20),rdef),repeat=2):
        su=-u/(1+u);tv=-v/(1+v)
        check(abs(su)<=rtrace and abs(tv)<=rtrace,'radius source')
        check(kval(b,u,v)==(1+u)*(1+v)*kval(a,su,tv),'globally unique original marks')
        check(hess(b,u,v)==hess(a,su,tv)/((1+u)**2*(1+v)**2),'mixed Hessian chart')
        if u==v==0:check(hess(b,0,0)==hess(a,0,0),'zero-source covariance')

# Four-column CMP119 approximation error bounds must transform with source
# convention: eps_def=(eps0,eps0+epsF,eps0+epsG,eps0+epsF+epsG+epsFG).
for da,db,dc,dd in product((-2,-1,0,1,2), repeat=4):
    eps=[abs(da),abs(db),abs(dc),abs(dd)]
    jt=deficit((da,db,dc,dd))
    limits=(eps[0],eps[0]+eps[1],eps[0]+eps[2],sum(eps))
    check(all(abs(jt[i])<=limits[i] for i in range(4)),'four-column error transport')

# A literal trace-to-deficit event-log quotient has no extra prefactor:
# K_B^def/K_A^def=(K_B^tr/K_A^tr) evaluated at the Möbius source chart.
Arows=[v for v in records if not v[3]]
Brows=[v for v in records if v[3]]
a=coeff(Arows);b=coeff(Brows)
for u,v in product((-rdef,Q(0),rdef), repeat=2):
    su=-u/(1+u);tv=-v/(1+v)
    ratio_def=Q(kval(deficit(b),u,v),kval(deficit(a),u,v))
    ratio_trace=Q(kval(b,su,tv),kval(a,su,tv))
    check(ratio_def==ratio_trace,'event log source ratio chart')

print('PASS',checks,'exact source-chart, mixed-Hessian, complex radius, CMP119 four-column error and conditional-F19 tests')
print('At radius r_def=9/109 original trace r=9/100 is preserved, unlike taking both r=9/100.')
print('NOT: full unfrozen SU(N) Haar numerical integration, selected CMP119/122 constrained T or original CMP116 absolute physical shell, or Clay YM gap.')
