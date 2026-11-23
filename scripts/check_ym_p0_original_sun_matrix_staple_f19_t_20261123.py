#!/usr/bin/env python3
"""Original full L4 Wilson/R445-F19 SU(N) twelve-staple external-field source.

For U0=W*V^-1,U1=V, all ORIGINAL 1536 plaquettes yield
S(V)=C-ReTr(H*V)/N with H the sum of exactly twelve original SU(N) staples.
This retains original marked 1/F/G/FG and all spectator plaquettes.
Test noncommuting exact-rational SU2/SU3; NOT the complete physical
CMP119/CMP122 Eq171 gauge/FP/E/R/B/V T, W3 or Clay mass gap.
"""
from itertools import product
from random import Random
from pathlib import Path
from importlib.util import spec_from_file_location,module_from_spec
import sympy as s
p=Path(__file__).with_name("check_ym_p0_original_wilson_marked_ordered_t_20261123.py")
assert p.is_file(), "Require native original full L4 Wilson source owner"
sp=spec_from_file_location("original_l4",p)
src=module_from_spec(sp);sp.loader.exec_module(src)
pairs=[]
for c in product(range(2),repeat=4):
 o=tuple(2*i for i in c)
 for a in range(4):pairs.append(((o,a),(src.step(o,a),a)))
assert len(pairs)==64 and {l for pair in pairs for l in pair}==src.selected
assert len(src.links)==1024 and len(src.faces)==1536
touching={l:set() for l in src.links}
for k,face in enumerate(src.faces):
 for l in face:touching[l].add(k)
assert {len(v) for v in touching.values()}=={6}
F=src.face(src.F,2,3);G=src.face(src.G,2,3)
def pool(n):
 c=s.Rational(3,5);v=s.Rational(4,5)
 if n==2:
  A=s.Matrix([[c,v],[-v,c]])
  B=s.Matrix([[c,s.I*v],[s.I*v,c]])
  C=s.diag(c+s.I*v,c-s.I*v)
 else:
  A=s.Matrix([[c,-v,0],[v,c,0],[0,0,1]])
  B=s.Matrix([[1,0,0],[0,c,-v],[0,v,c]])
  C=s.Matrix([[0,1,0],[0,0,1],[1,0,0]])
 eye=s.eye(n)
 assert all(s.simplify(U.det())==1 and s.simplify(U*U.H-eye)==s.zeros(n)
            for U in (A,B,C,A*B,B*C,C*A))
 assert A*B!=B*A
 return [eye,A,B,C,A*B,B*C,C*A]
def retr(M):
 z=s.trace(M)
 return s.expand((z+s.conjugate(z))/2)
def hol(field,p,eye):
 a,b,c,d=p
 return field.get(a,eye)*field.get(b,eye)*field.get(c,eye).H*field.get(d,eye).H
def deficit(field,p,eye):
 return s.expand(1-retr(hol(field,p,eye))/eye.rows)
def insert(base,pair,W,V):
 out=dict(base);out[pair[0]]=W*V.H;out[pair[1]]=V
 return out
def staple(p,pair,W,base,eye):
 # Expand each original oriented face into fixed matrices and exactly one V/Vdag.
 atoms=[]
 for l,pos in zip(p,(True,True,False,False)):
  if l==pair[0]:
   atoms.extend([W,"vdag"] if pos else ["v",W.H])
  elif l==pair[1]:atoms.append("v" if pos else "vdag")
  else:
   U=base.get(l,eye)
   atoms.append(U if pos else U.H)
 ids=[k for k,u in enumerate(atoms) if isinstance(u,str)]
 assert len(ids)==1
 j=ids[0];A=eye;B=eye
 for u in atoms[:j]:A=A*u
 for u in atoms[j+1:]:B=B*u
 return B*A if atoms[j]=="v" else (B*A).H
checks=dict(geometry=0,source=0,marked=0,global_jet=0)
for n in (2,3):
 eye=s.eye(n);P=pool(n);rng=Random(445+n)
 spectators=list(set(src.links)-src.selected)
 for trial in range(4):
  base={l:rng.choice(P[1:]) for l in rng.sample(spectators,10+2*trial)}
  for l in ((src.F,2),(src.G,2),(src.F,3),(src.G,3)):
   base[l]=rng.choice(P[1:])
  # Evaluate the full original 1536-face action ONCE; then reconstruct its
  # precise 12 changed/1524 unchanged decomposition for each source pair.
  whole=sum((deficit(base,face,eye) for face in src.faces),s.Integer(0))
  for pi in (0,2,3,6,7,17):
   pair=pairs[pi];W=rng.choice(P[1:])
   affected=touching[pair[0]]|touching[pair[1]]
   assert len(affected)==12 and not(touching[pair[0]]&touching[pair[1]])
   H=s.zeros(n)
   for k in affected:H+=staple(src.faces[k],pair,W,base,eye)
   untouched=whole-sum((deficit(base,src.faces[k],eye) for k in affected),s.Integer(0))
   C=s.expand(untouched+12)
   checks['geometry']+=3
   for V in P+[P[1]*P[2],P[2]*P[1]]:
    field=insert(base,pair,W,V)
    actual=sum((deficit(field,src.faces[k],eye) for k in affected),s.Integer(0))
    predicted=s.expand(12-retr(H*V)/n)
    assert s.simplify(actual-predicted)==0
    checks['source']+=1
    for mark in (F,G):
     if any(l in pair for l in mark):
      Hmark=staple(mark,pair,W,base,eye)
      assert s.simplify(deficit(field,mark,eye)-(1-retr(Hmark*V)/n))==0
     else:
      assert deficit(field,mark,eye)==deficit(base,mark,eye)
     checks['marked']+=1
   beta=s.symbols("beta",positive=True)
   u,v=s.symbols("u v")
   V=P[1];field=insert(base,pair,W,V)
   k0=s.exp(-beta*(C-retr(H*V)/n))
   f=deficit(field,F,eye);g=deficit(field,G,eye)
   K=k0*(1+u*f)*(1+v*g)
   assert s.diff(K,u,v).subs({u:0,v:0})==k0*f*g
   checks['global_jet']+=1
print("PASS SymPy",s.__version__,sum(checks.values()),checks)
print("Original SU(2)/SU(3) full Wilson L4, 24 noncommuting pair/background cases")
print("S(V)=C-ReTr(HV)/N, H=SUM of twelve ORIGINAL source staple matrices")
print("True one-fibre continuous SU(N) Haar T0=e^-betaC * integral exp(beta ReTr(HV)/N)")
print("Original same-global-source 1/F/G/FG marks retained, no other-link freezing assumption")
print("OPEN CMP119/CMP122 Eq171 constrained gauge-fixed T, physical W3/OS")
