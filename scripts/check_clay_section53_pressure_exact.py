#!/usr/bin/env python3
"""Exact algebraic negative controls for original NS modal pressure.

Not a PDE theorem or a substitute for Lean. All Fourier data are Gaussian
rationals; checks retain three physical components, zero output and signs.
"""
from fractions import Fraction as Q
from itertools import product
import json

class Z:
    def __init__(self, a=0, b=0):
        self.a, self.b = Q(a), Q(b)
    def __add__(self, o):
        return Z(self.a+o.a,self.b+o.b)
    def __neg__(self): return Z(-self.a,-self.b)
    def __sub__(self,o): return self+-o
    def __mul__(self,o): return Z(self.a*o.a-self.b*o.b,self.a*o.b+self.b*o.a)
    def __truediv__(self,o):
        d=o.a*o.a+o.b*o.b
        return Z((self.a*o.a+self.b*o.b)/d,(self.b*o.a-self.a*o.b)/d)
    def __eq__(self,o): return isinstance(o,Z) and self.a==o.a and self.b==o.b
    def __repr__(self): return f'({self.a},{self.b})'

ZERO=Z(); I=Z(0,1)
def dot(k,u): return sum((Z(x)*y for x,y in zip(k,u)), ZERO)
def pressure(k,u,v):
    m=sum(x*x for x in k)
    return -(dot(k,u)*dot(k,v))/Z(m) if m else ZERO

def raw(k,u,v): return tuple(I*dot(k,u)*x for x in v)
def projected(k,u,v):
    r=raw(k,u,v)
    m=sum(x*x for x in k)
    if m==0:return r
    d=dot(k,r)
    return tuple(x-Z(t)*d/Z(m) for t,x in zip(k,r))
def quad(k,u,v):
    r=raw(k,u,v);p=pressure(k,u,v)
    return tuple(-x-I*Z(c)*p for c,x in zip(k,r))

def vec(seed):
    return tuple(Z(seed*(j+1)-2, (j-1)*(seed+1)) for j in range(3))

def check():
    count=0; pressure_count=0
    for k in product((-2,-1,0,1,2),repeat=3):
      for seed in (-2,-1,0,1,2):
        u,v,u1,v1=(vec(seed),vec(seed+1),vec(seed-1),vec(2-seed))
        assert tuple(-x for x in projected(k,u,v))==quad(k,u,v)
        assert pressure(k,u,v)-pressure(k,u1,v1)==pressure(k,tuple(a-b for a,b in zip(u,u1)),v)+pressure(k,u1,tuple(a-b for a,b in zip(v,v1)))
        assert pressure(k,u,v)==pressure(k,v,u)
        if k==(0,0,0):assert pressure(k,u,v)==ZERO
        count+=1;pressure_count+=4
    return {'cases':count,'identities':pressure_count,'zero_frequency':5,'carrier':'Gaussian rationals, 3-component physical vectors','status':'PASS'}
if __name__=='__main__':
    r=check()
    print(json.dumps(r,sort_keys=True,separators=(',',':')))
