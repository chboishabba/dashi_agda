#!/usr/bin/env python3
"""Exact adverse geometry regressions. Not theorem-prover receipts."""
from fractions import Fraction as F
from itertools import product
import json

class Dual:
    def __init__(self,a,b=0): self.a,self.b=F(a),F(b)
    def __add__(self,o): return Dual(self.a+o.a,self.b+o.b)
    def __neg__(self): return Dual(-self.a,-self.b)
    def __sub__(self,o): return self+-o
    def __mul__(self,o): return Dual(self.a*o.a,self.a*o.b+self.b*o.a)
    def inv(self):
        assert self.a
        return Dual(1/self.a,-self.b/(self.a*self.a))
    def __eq__(self,o): return isinstance(o,Dual) and (self.a,self.b)==(o.a,o.b)
    def __repr__(self): return f'{self.a}+{self.b}e'
    def __pow__(self,n):
        p=Dual(1)
        for _ in range(n):p=p*self
        return p

def test_ym():
    cases=0
    for height in range(0,10):
      for k in range(height+1):
        f=[F(((-1)**i)*(i+1),i+2) for i in range(height)]
        g=[F(((-1)**(i+1))*(2*i+1),i+3) for i in range(height)]
        whole=sum((f[i]*g[j] for i in range(height) for j in range(height)), F(0))
        triangle=sum((f[i]*g[j] for i in range(k) for j in range(k-i)), F(0))
        complement=sum((f[i]*g[j] for i in range(height) for j in range(height) if i+j>=k),F(0))
        assert whole-triangle==complement
        cases+=1
    return cases

def test_bsd():
    cases=0
    for a,b,x in product([F(1,3),F(2,3),F(3,2)], [F(1,2),F(5,3)], [F(0),F(1,5),F(3),F(-2)]):
      h=[F(1)]
      q=[F(1)]
      for n in range(1,11):
        h.append(a*h[-1]+b**n)
        q.append(a*b*q[-1]+h[n]*x**n)
      for n in range(11):
        poly=h[n]*x**(n+2)-h[n+1]*x**(n+1)+(a*b)**(n+1) if n<10 else None
        if poly is None:break
        assert poly==(x-a)*(x-b)*q[n]
        if x>=0:assert q[n]>0
        cases+=1
    return cases

def test_hodge():
    cases=0
    seeds=[Dual(2,1),Dual(-3,F(1,3)),Dual(F(1,2),-2),Dual(4,0)]
    for i,j,k in product(seeds,repeat=3):
      rij=i*j.inv();rjk=j*k.inv();rik=i*k.inv()
      assert rij*rjk==rik
      assert rij*(j*i.inv())==Dual(1)
      for d in range(7):
        p=Dual(F(3,2),F(2,5))
        assert (p*i.inv()**d)*rij**d == p*j.inv()**d
        cases+=1
    return cases

def parity_mask(x):
    p=sum(x)%2
    return tuple(b^p for b in x)
def test_pnp():
    cases=0
    for n in [2,4,6,8]:
      for x in product([0,1],repeat=n):
        assert parity_mask(parity_mask(x))==x
        cases+=1
    for a,b,c in product([0,1],repeat=3):
      def toffoli(t):return (t[0],t[1],t[2]^(t[0]&t[1]))
      assert toffoli(toffoli((a,b,c)))==(a,b,c)
      cases+=1
    return cases

if __name__=='__main__':
    result={'YM_triangle':test_ym(),'BSD_crossing':test_bsd(),'Hodge_dual_ring':test_hodge(),'PNP_shared':test_pnp(),'status':'PASS'}
    print(json.dumps(result,sort_keys=True,separators=(',',':')))
