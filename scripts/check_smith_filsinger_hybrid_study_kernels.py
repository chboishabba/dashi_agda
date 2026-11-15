#!/usr/bin/env python3
"""Exact conditional math for Smith/Filsinger hybrid source and observations.
No source-study's empirical claim is asserted from this file.
"""
from math import sqrt
import sympy as sp

def phasorNullMinimumExact():
    a,b,c=sp.symbols('a b c',real=True)
    intensity=a*a+b*b+2*a*b*c
    assert sp.simplify(intensity.subs(c,-1)-(a-b)**2)==0
    assert sp.simplify(intensity.subs(c,1)-(a+b)**2)==0
    return True

def freeSingleModeRingdownFixedFrequencyExact():
    t,w0,g=sp.symbols('t omega0 gamma',positive=True,real=True)
    damped=sp.sqrt(w0*w0-g*g)
    q=sp.exp(-g*t)*sp.cos(damped*t)
    assert sp.simplify(sp.diff(q,t,2)+2*g*sp.diff(q,t)+w0*w0*q)==0
    return True

def twoModeNonlinearPumpEnergyIdentityExact():
    t=sp.symbols('t',real=True)
    x,y,v,w=[sp.Function(z)(t) for z in ('x','y','v','w')]
    k1,k2,coupling,quartic=[sp.Function(z)(t) for z in ('k1','k2','coupling','quartic')]
    driver,natural,r1,r2=sp.symbols('driver natural r1 r2',real=True)
    U=k1*x*x/2+k2*y*y/2+coupling*x*x*y+quartic*x**4/4
    H=(v*v+w*w)/2+U
    dynamics={sp.diff(x,t):v,sp.diff(y,t):w,
              sp.diff(v,t):-sp.diff(U,x)-r1*v+driver,
              sp.diff(w,t):-sp.diff(U,y)-r2*w+natural}
    modwork=sp.diff(k1,t)*x*x/2+sp.diff(k2,t)*y*y/2+sp.diff(coupling,t)*x*x*y+sp.diff(quartic,t)*x**4/4
    rhs=driver*v+natural*w-r1*v*v-r2*w*w+modwork
    assert sp.simplify(sp.diff(H,t).subs(dynamics)-rhs)==0
    passive=rhs.subs({driver:0,natural:0,sp.diff(k1,t):0,
                      sp.diff(k2,t):0,sp.diff(coupling,t):0,sp.diff(quartic,t):0})
    assert sp.simplify(passive+r1*v*v+r2*w*w)==0
    return True

def twoHopEnvironmentalFlight(start,delay1,delay2):
    if delay1<0 or delay2<0:raise ValueError('noncausal propagation')
    first=start+delay1;second=first+delay2
    assert start<=first<=second
    return first,second

def actualGainRequiresExternalPort():
    # Counterexample: useful>driver but independent natural input is zero.
    driver,natural,modulator,stored=12,0,100,3
    useful,heat,finalStored=50,40,25
    assert driver+natural+modulator+stored==useful+heat+finalStored
    return useful>driver and natural==0

def run():
    for fn in (phasorNullMinimumExact,freeSingleModeRingdownFixedFrequencyExact,
               twoModeNonlinearPumpEnergyIdentityExact,actualGainRequiresExternalPort):
        assert fn()
    assert twoHopEnvironmentalFlight(0,5,7)==(5,12)
    print('PASS: four conditional exact kernels and causal two-hop check')

if __name__=='__main__':run()
