#!/usr/bin/env python3
"""Exact original Griess source six corrected-shear character discriminator.

Original authority: Robert L. Griess Jr., J. Algebra 131 (1990) 281-293
DOI 10.1016/0021-8693(90)90176-O, original g, Moufang and Albert.
Explicit source h(x) corrections: pre-existing Lean #52 / Agda #1239.
A 26-point grade permutation is NOT the 26D traceless Albert operator.

Six fixed-point/cyclotomic character checks use only standard library.
Optional --source-products imports the REPO'S EXISTING Griess original
source checker and tests all 729 literal tau-real Jordan source products
for each of the two representative shears e01/e02 (needs SymPy).
Kernel status is OPEN; no full SL3 section/intertwiner theorem claimed.
"""
from itertools import product
from collections import Counter
import sys
V=tuple(product(range(3),repeat=3))
shears=((0,1),(0,2),(1,0),(1,2),(2,0),(2,1))
def shear(x,i,j):
 y=list(x);y[i]=(y[i]+y[j])%3
 return tuple(y)
def h(x,i,j):
 a,b,c=x
 return {(0,1):c*(1-b*b),(0,2):0,(1,0):c*(1-a*a),
         (1,2):a*(c*c-1),(2,0):0,(2,1):a*(b*b-1)}[i,j]%3
for i,j in shears:
 f=[x for x in V if shear(x,i,j)==x]
 counts=Counter(h(x,i,j) for x in f)
 assert len(f)==9 and counts[1]==counts[2]
 tr27=counts[0]-counts[2];tr26=tr27-1
 assert tr26==(-1 if (i,j) in ((0,1),(1,0),(1,2),(2,1)) else 8)
 assert len([x for x in f if x!=(0,0,0)])==8
 print(f'PASS e{i}{j}: fixed phases {[counts[k] for k in range(3)]}, tau-real Albert J0 trace {tr26}, grade26 trace 8')
assert -1!=8
if '--source-products' in sys.argv:
 from pathlib import Path
 import runpy
 import sympy as s
 root=Path(__file__).resolve().parent
 choices=(root/'check_griess1990_crossprover_standalone_certificate.py',
          root/'check_griess1990_rational_triality_crossprover_certificate.py')
 donor=next((p for p in choices if p.is_file()),None)
 if donor is None:raise SystemExit('missing preexisting Griess original source checker')
 data=runpy.run_path(str(donor))
 basis=data['basis'];coords=data['source_coords'];prod=data['srcprod']
 qmul=data['qmul'];qadd=data['qadd'];omega=data['omega'];zero=data['Z']
 def act(v,i,j):
  ans={}
  for grade,coeff in v.items():
   y=shear(grade,i,j)
   ans[y]=qadd(ans.get(y,zero),qmul(omega[h(grade,i,j)],coeff))
  return {k:x for k,x in ans.items() if x!=zero}
 for i,j in ((0,1),(0,2)):
  T=s.Matrix.hstack(*[coords(act(v,i,j)) for v in basis])
  assert T**3==s.eye(27) and T[:,0]==s.eye(27)[:,0]
  assert s.trace(T)==(0 if (i,j)==(0,1) else 9)
  for a,b in product(range(27),repeat=2):
   assert coords(act(prod(basis[a],basis[b]),i,j))==coords(prod(act(basis[a],i,j),act(basis[b],i,j)))
  print(f'PASS literal original tau-real e{i}{j}: 729/729 Jordan products, order3, trace27={s.trace(T)}')
print('NO selected six-shear full-J0 grade-permutation module weld: trace mismatch e01/e10/e12/e21')
print('BOUNDARY: alternative central-character lifts, C13-only and native J0 full-group remain separately typed')
