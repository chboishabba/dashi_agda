#!/usr/bin/env python3
"""Independent Q8 noncommutative reference: original periodic 4D blocked positive links.

Checks true L-step edge products, exact non-Abelian gauge cancellation,
coarse M*L endpoint matching, and a deliberately wrong missing-inverse control.
This is not an Agda kernel proof, Wilson pushforward, or continuum mass gap.
"""
from itertools import product

E = (1, 0, 0, 0)

def mul(x, y):
    a,b,c,d=x; e,f,g,h=y
    return (a*e-b*f-c*g-d*h, a*f+b*e+c*h-d*g,
            a*g-b*h+c*e+d*f, a*h+b*g-c*f+d*e)

def inv(x):
    a,b,c,d=x
    return (a,-b,-c,-d)

UNITS = [E, (-1,0,0,0), (0,1,0,0), (0,-1,0,0),
         (0,0,1,0), (0,0,-1,0), (0,0,0,1), (0,0,0,-1)]

def sample(site, axis, key):
    weight = sum((i+1)*(13+7*i)*v for i,v in enumerate(site))
    return UNITS[(weight + axis*5 + key*3) % len(UNITS)]

def verify(m, L):
    n = m*L
    def gamma(site): return sample(site,0,2)
    def field(site,axis): return sample(site,axis,1)
    def step(site,axis):
        z=list(site); z[axis]=(z[axis]+1)%n
        return tuple(z)
    def transformed(site,axis):
        return mul(mul(gamma(site),field(site,axis)),inv(gamma(step(site,axis))))
    def wrong(site,axis):
        return mul(mul(gamma(site),field(site,axis)),gamma(step(site,axis)))
    def path(start,axis,fn):
        val=E;here=start
        for _ in range(L):
            val=mul(val,fn(here,axis));here=step(here,axis)
        return val,here
    total=0;negative=0
    for coarse in product(range(m),repeat=4):
        start=tuple(x*L for x in coarse)
        for axis in range(4):
            target=list(coarse);target[axis]=(target[axis]+1)%m
            expected=tuple(x*L for x in target)
            U,end=path(start,axis,field)
            U_g,end_g=path(start,axis,transformed)
            U_wrong,_=path(start,axis,wrong)
            assert end==end_g==expected
            assert U_g==mul(mul(gamma(start),U),inv(gamma(end)))
            if U_wrong!=U_g:negative+=1
            total+=1
    assert negative>0,(m,L)
    print(f'coarse M={m}, block L={L}, fine={n}, coarse bonds={total}; '
          f'endpoint/gauge PASS; bad-inverse rejected {negative}/{total}')

if __name__=='__main__':
    for M,L in ((1,3),(2,2),(2,3),(3,2),(4,2)):
        verify(M,L)
    print('REFERENCE ONLY: not Agda or physical YM continuum')
