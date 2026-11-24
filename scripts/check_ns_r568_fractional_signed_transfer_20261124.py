from itertools import product
from random import Random
from sympy import I, Matrix, conjugate, symbols, expand, diff
rng=Random(369)
ks=[k for k in product(range(-1,2),repeat=3) if any(k)]
def neg(k): return tuple(-x for x in k)
def norm2(k): return sum(x*x for x in k)
weights={j:symbols('w'+str(j),real=True) for j in range(1,4)}
checks=0; wchecks=0
for seed in range(4):
 u={}
 for k in ks:
  if k in u: continue
  v=Matrix([rng.randrange(-2,3)+I*rng.randrange(-2,3) for _ in range(3)])
  K=Matrix(k); v=(v-K*(K.dot(v))/norm2(k)).applyfunc(expand)
  u[k]=v;u[neg(k)]=v.conjugate()
 for k in ks: assert expand(Matrix(k).dot(u[k]))==0
 direct=0; paired=0; zero=0
 for p in ks:
  for q in ks:
   k=tuple(a+b for a,b in zip(p,q))
   if k not in u: continue
   A=expand(I*u[p].dot(Matrix(q))*u[q].dot(u[k].conjugate()))
   B=expand(I*u[neg(p)].dot(Matrix(k))*u[k].dot(u[q].conjugate()))
   assert expand(B+conjugate(A))==0; checks+=1
   ar=A.as_real_imag()[0]; wk,wq=weights[norm2(k)],weights[norm2(q)]
   direct-=2*wk*ar; paired-=(wk-wq)*ar; zero+=ar
 assert expand(direct-paired)==0 and expand(zero)==0; wchecks+=1
s,nu=symbols('s nu', positive=True); E=3+s+s**2; T=2-s; D=(T-diff(E,s))/(2*nu)
assert expand(32*E*D-8/nu*(-diff(E**2,s)+2*E*T))==0
print('ordered conjugate involution checks', checks, 'weighted transfer identities',wchecks,'formal energy identity PASS')
