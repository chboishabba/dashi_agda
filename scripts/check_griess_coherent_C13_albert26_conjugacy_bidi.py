#!/usr/bin/env python3
"""EXACT coherent-SL3 order13 bridge back to earlier positive Albert J0 C13.

Original roots Sah 1974; Griess 1976 (splitting); Griess 1990 (M81/Albert).
Source M81 test is standalone. To test the SAME literal native rational
26D Albert, provide three existing JSON certificates as argv[1:]:
  source_to_native_27.json  native_traceless_order13_26.json  old_intertwiner26.json
These are INPUTS, not invented evidence. No Lean/Agda kernel claim.
"""
from itertools import product
from pathlib import Path
import json,sys
V=tuple(product(range(3),repeat=3))
S=((0,1),(1,2),(2,0))
L={(0,1):(0,0,0),(1,2):(2,0,0),(2,0):(0,1,0)}
def shear(x,i,j):
 y=list(x);y[i]=(y[i]+y[j])%3;return tuple(y)
def phase(x,i,j):
 a,b,c=x
 return {(0,1):c*(1-b*b),(1,2):a*(c*c-1),(2,0):0}[i,j]%3
def shift(m,lam):
 x,a=m
 return x,(a+sum(lam[t]*x[t] for t in range(3)))%3
def word(m,coherent=False):
 x,a=m
 for i,j in S:
  y=shear(x,i,j)
  a=(a+phase(x,i,j)+(sum(L[i,j][t]*y[t] for t in range(3)) if coherent else 0))%3
  x=y
 return x,a
mu=(2,1,0);nu=(1,1,2)
for m in product(V,range(3)):
 assert word(m,True)==shift(word(m,False),mu)
 negnu=tuple((-a)%3 for a in nu)
 assert word(m,True)==shift(word(shift(m,negnu),False),nu)
print('PASS 81/81 SAME source old/new C13 words, mu=(2,1,0), conjugator nu=(1,1,2)')
if len(sys.argv)==1:
 print('To pay SAME native Albert26 matrix receipt pass three original JSON certificates')
 raise SystemExit(0)
if len(sys.argv)!=4:raise SystemExit('usage: script source_map27.json native_oldB26.json oldX26.json')
import sympy as s
source=json.loads(Path(sys.argv[1]).read_text())
old=json.loads(Path(sys.argv[2]).read_text())
xdata=json.loads(Path(sys.argv[3]).read_text())
A=s.Matrix([[s.Rational(v) for v in row] for row in source['full_27_by_27_native_rational_transport']])
Ai=s.Matrix([[s.Rational(v) for v in row] for row in source['explicit_native_to_source_inverse']])
B=s.Matrix([[s.Rational(v) for v in row] for row in old['native_albert26_traceless_order13_matrix']])
X=s.Matrix([[s.Rational(v) for v in row] for row in xdata['native_traceless_albert_to_two_grade_cycle_intertwiner']])
assert A*Ai==s.eye(27) and X.det()==-s.Rational(729,4096)
root=Path(__file__).resolve().parent
from runpy import run_path
donors=(root/'check_griess1990_crossprover_standalone_certificate.py',
        root/'check_griess1990_rational_triality_crossprover_certificate.py')
donor=next((x for x in donors if x.is_file()),None)
if donor is None:raise SystemExit('missing original source tau-real checker')
d=run_path(str(donor))
coords=d.get('coords',d.get('source_coords'))
omega=d['omega'];qmul=d['qmul'];basis=d['basis']
D=s.Matrix.hstack(*[coords({x:qmul(omega[sum(nu[k]*x[k] for k in range(3))%3],v)
                            for x,v in b.items()}) for b in basis])
assert D.det()==1
K=A*D*Ai
P=s.zeros(27,26);P[0,0]=1;P[1,0]=-1;P[1,1]=1;P[2,1]=-1
Q=s.zeros(26,27);Q[0,0]=1;Q[1,2]=-1
for j in range(24):P[j+3,j+2]=Q[j+2,j+3]=1
T=Q*K*P
assert K*P==P*T and T.det()==1
Y=T*X
C=s.zeros(26)
for block in (0,13):
 for j in range(13):C[block+(j+1)%13,block+j]=1
assert B*X==X*C
assert (T*B*T.inv())*Y==Y*C and Y.det()==-s.Rational(729,4096)
print('PASS actual native J0 coherent-word conjugator det1; new BX=XP, det X=-729/4096')
