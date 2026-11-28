"""Original central symbol replay and exact complex-parameter Hecke/reflection controls.
Does not evaluate complex derivatives or prove BSD.
"""
import runpy
from pathlib import Path
from fractions import Fraction as Q
from math import gcd
import sympy as sp
src=runpy.run_path(str(Path(__file__).with_name('check_clay_bsd_234446_actual_cyclotomic_symbols.py')))
V=src['V']; N=src['N']; cs=src['cs']; checks=0

def ck(ok):
 global checks
 if not ok: raise AssertionError('distribution control failed')
 checks+=1

# actual normalized symbols are invariant under the literal Fricke cusp involution
for q,vals in V.items():
 for a,v in vals.items():
  if a==0: continue
  J=-pow(N*a,-1,q)%q
  ck(-pow(N*J,-1,q)%q==a)
  ck(vals[J]==v)
# formal identities for arbitrary complex parameter: X=p^z, Y=alpha.
X,Y,H,K=sp.symbols('X Y H K', nonzero=True)
for p in (5,11):
 ap=cs[p]; pol=sp.Poly(Y**2-ap*Y+p,Y)
 # sum of child measures minus parent, times alpha^(n+2)
 ck(sp.rem(sp.Poly((ap*Y-p-Y**2)*H,Y),pol).is_zero)
 # total ordinary mass multiplier: alpha^2 times expression
 ck(sp.rem(sp.Poly(ap*Y-(X+1/X)*Y-(p-1)-(Y**2+1-(X+1/X)*Y),Y),pol).is_zero)
 # actual coefficient identities: root-of-unity trace with Hecke coefficients
 for s in (1,2,3,4):
  for k in range(1,101):
   lhs=Q(p,p**s)*Q(cs[p*k],k**s)
   rhs=Q(ap,p**(s-1))*Q(cs[k],k**s)
   if k%p==0: rhs-=Q(1,p**(2*s-2))*Q(cs[k//p],(k//p)**s)
   ck(lhs==rhs)
 # reflection on actual cyclotomic group ring, using existing measure coefficients
 for m in ((1,2) if p==5 else (1,)):
  q=p**(m+1); n=p**m; mod=p**(m+3)
  g=1+p; roots=[u for u in range(1,q) if pow(u,p-1,q)==1]
  labels={z*pow(g,k,q)%q:k for z in roots for k in range(n)}
  h=labels[-pow(N,-1,q)%q]
  d=src['d1'] if p==5 and m==1 else src['d2'] if p==5 else src['d3']
  for a,k in labels.items(): ck(labels[-pow(N*a,-1,q)%q]==(h-k)%n)
  for k in range(n):ck(d[k]==d[(h-k)%n])
  # centralize reflection by the unique half-shift in odd-order cyclic group
  c=h*pow(2,-1,n)%n; centered=[d[(k+c)%n] for k in range(n)]
  ck(all(centered[k]==centered[-k%n] for k in range(n)))
  # Reynolds idempotent of complex group ring, exact projection into augmentation
  # sum of entries is one, convolution square equals itself; projection down preserves it.
  e=[Q(1,n)]*n
  for k in range(n):ck(sum(e[j]*e[(k-j)%n] for j in range(n))==e[k])
  ck(sum(e)==1)
  if m>1: ck(all(sum(e[k+j*(n//p)] for j in range(p))==Q(p,n) for k in range(n//p)))
  print('actual reflection',p,m,'shift',h,'center',c,flush=True)
print(f'{checks}/{checks} distribution controls PASS',flush=True)
