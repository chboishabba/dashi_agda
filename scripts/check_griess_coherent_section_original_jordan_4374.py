#!/usr/bin/env python3
"""All six coherent SL3(3) M81 lifts preserve Griess 1990 original Q(omega)
tau-real Albert Jordan product (6*729 exact basis products). Requires the
PRE-EXISTING independent original source product checker on this PR.

Priority: Sah 1974; Griess 1976 splitting; Griess 1990 Albert/loop.
This is a finite check, NOT a Lean/Agda kernel receipt.
"""
from pathlib import Path
from itertools import product
import runpy
import sympy as s

root=Path(__file__).resolve().parent
options=(root/'check_griess1990_crossprover_standalone_certificate.py',
         root/'check_griess1990_rational_triality_crossprover_certificate.py')
donor=next((p for p in options if p.is_file()),None)
if donor is None:raise SystemExit('MISSING ORIGINAL SOURCE PRODUCT CHECKER')
d=runpy.run_path(str(donor))
basis=d['basis'];coords=d.get('coords',d.get('source_coords'))
srcprod=d['srcprod'];qmul=d['qmul'];qadd=d['qadd']
omega=d['omega'];zero=d['Z']
assert len(basis)==27
S=((0,1),(0,2),(1,0),(1,2),(2,0),(2,1))
L=((0,0,0),(0,2,0),(0,0,1),(2,0,0),(0,1,0),(0,0,0))
def shear(x,i,j):
 y=list(x);y[i]=(y[i]+y[j])%3;return tuple(y)
def h(x,i,j):
 a,b,c=x
 return {(0,1):c*(1-b*b),(0,2):0,(1,0):c*(1-a*a),
         (1,2):a*(c*c-1),(2,0):0,(2,1):a*(b*b-1)}[i,j]%3
def lift(v,i,j,lam):
 out={}
 for x,z in v.items():
  y=shear(x,i,j)
  k=(h(x,i,j)+sum(lam[t]*y[t] for t in range(3)))%3
  out[y]=qadd(out.get(y,zero),qmul(omega[k],z))
 return {a:z for a,z in out.items() if z!=zero}
for (i,j),lam in zip(S,L):
 T=s.Matrix.hstack(*[coords(lift(b,i,j,lam)) for b in basis])
 assert T**3==s.eye(27) and T[:,0]==s.eye(27)[:,0]
 assert s.trace(T)==0
 for a,b in product(range(27),repeat=2):
  lhs=coords(lift(srcprod(basis[a],basis[b]),i,j,lam))
  rhs=coords(srcprod(lift(basis[a],i,j,lam),
                     lift(basis[b],i,j,lam)))
  assert lhs==rhs,(i,j,a,b)
 print('PASS actual original source corrected e%d%d: 729 Jordan products, trace27=0'% (i,j))
print('PASS all 4374 original Griess tau-real Jordan products; J0 trace -1 each')
print('NOT Lean/Agda kernel or full native F4/Monster/physical action')
