#!/usr/bin/env python3
"""H07 exact source-formula certificate: selected triangular F3 pivot.
Full prefix partitions, no quadratic pair enumeration. Local SymPy only.
"""
from itertools import product
import sympy as sy
s,t,u,a0,a1,a2,b0,b1,b2=sy.symbols('s t u a0 a1 a2 b0 b1 b2')
orig=(s,t,u,a0,a1,a2,b0,b1,b2)
def reduce3(expr):
 p=sy.Poly(sy.expand(expr),*orig,domain=sy.GF(3))
 result=sy.Poly(0,*orig,domain=sy.GF(3))
 for powers,coefficient in p.terms():
  e=list(powers)
  for i in range(3):
   if e[i]>=2:e[i]%=2 # signed s,t,u have squares equal 1
  result+=sy.Poly(int(coefficient)*sy.prod(x**n for x,n in zip(orig,e)),*orig,domain=sy.GF(3))
 return result
def pivot_expr(w):
 v0,v1,v2,x0,x1,x2,y0,y1,y2=w
 xx=-x0*v0; yy=-y0*v0
 return (v0,v1*v0,v2*v0,xx,x1+v1*xx,x2+v2*xx,yy,y1+v1*yy,y2+v2*yy)
trans=pivot_expr(orig)
for i,(left,right) in enumerate(zip(pivot_expr(trans),orig)):
 assert reduce3(left-right).is_zero,i
for i,expr in enumerate(trans):
 assert expr.free_symbols <= set(orig[:i+1])
 unit=sy.diff(expr,orig[i])
 assert reduce3(unit*unit-1).is_zero,(i,unit)
 assert unit.free_symbols <= set(orig[:i])
print('PASS symbolic involution and all 9 leading-unit triangular coordinate equations')
print('Diagonal:',[sy.diff(v,orig[i]) for i,v in enumerate(trans)])
def pivot(x):
 v0,v1,v2,x0,x1,x2,y0,y1,y2=x
 xx=-x0*v0%3;yy=-y0*v0%3
 return v0,v1*v0%3,v2*v0%3,xx,(x1+v1*xx)%3,(x2+v2*xx)%3,yy,(y1+v1*yy)%3,(y2+v2*yy)%3
states=[v+a+b for v in product((1,2),repeat=3) for a in product(range(3),repeat=3) for b in product(range(3),repeat=3)]
images=[pivot(x) for x in states]
assert len(states)==len(set(images))==5832
assert all(pivot(y)==x for x,y in zip(states,images))
for k in range(10):
 quotient={}
 for x,y in zip(states,images):
  p,q=x[:k],y[:k]
  if p in quotient:assert quotient[p]==q
  else:quotient[p]=q
 assert len(set(quotient.values()))==len(quotient)==2**min(k,3)*3**max(0,k-3)
 print('depth',k,'classes',len(quotient),'fibre',5832//len(quotient))
print('All-pairs covered:',5832*5831//2)
order=(0,4,1,2,3,5,6,7,8)
seen={}
for x,y in zip(states,images):
 key=tuple(x[i] for i in order[:2])
 out=tuple(y[i] for i in order[:2])
 if key in seen and seen[key][1]!=out:
  print('PASS wrong-order counterexample:',seen[key],(x,out))
  break
 seen[key]=(x,out)
else:raise AssertionError('no negative control')
print('SymPy',sy.__version__)
