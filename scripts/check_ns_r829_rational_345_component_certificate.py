#!/usr/bin/env python3
"""R829 exact component certificate for the rational 3-4-5 snapshot.

This expands R828 into finite, exact rows suitable for repository reification:
velocity, projected nonlinearity, helical +/- velocity and forcing, fixed-output
mixed/commutator vectors, coherent work, production and dissipation.

The script deliberately recomputes the formulas rather than importing an
already-summed R828 result.  Every emitted scalar is rational.
"""
from functools import lru_cache
from itertools import product
from sympy import I, Matrix, Rational, S, conjugate, expand, simplify, sqrt
import json

CUT=4
MODES=frozenset(product(range(-CUT,CUT+1),repeat=3))-{(0,0,0)}
ZERO=Matrix([0,0,0])
SEEDS={
 (3,0,0):Matrix([0,2+2*I,-2-I]),
 (0,4,0):Matrix([2+2*I,0,2+2*I]),
 (3,4,0):Matrix([6*I,-Rational(9,2)*I,-2+2*I]),
}
def neg(k):return tuple(-x for x in k)
def add(a,b):return tuple(x+y for x,y in zip(a,b))
def sub(a,b):return tuple(x-y for x,y in zip(a,b))
def weight(k):return 2**((max(map(abs,k))-1).bit_length())
def project(k,v):
 m=Matrix(k); return simplify(v-m*(m.dot(v)/m.dot(m)))
def cv(v): return [str(simplify(x)) for x in v]
def qstr(x): return str(simplify(x))

u={}
for k,v in SEEDS.items():
 u[k]=v;u[neg(k)]=v.applyfunc(conjugate)

@lru_cache(None)
def force(k):
 if k not in MODES:return ZERO
 raw=ZERO
 for p,v in u.items():
  q=sub(k,p)
  if q in u:raw+=v.dot(Matrix(q))*u[q]
 return simplify(-I*project(k,raw))

active=set(u)
for p in u:
 for q in u:
  k=add(p,q)
  if k in MODES and force(k)!=ZERO:active.add(k)
# also retain any input mode needed by a nonzero fixed-output cell
expanded=set(active)
for k in tuple(active):
 for p in u:
  q=sub(k,p)
  if q in u:expanded|={p,q}
active=expanded
norm={k:sqrt(sum(z*z for z in k)) for k in active}
assert all(x.is_Rational for x in norm.values())

@lru_cache(None)
def hel(k,forcing,sign):
 v=force(k) if forcing else u.get(k,ZERO)
 if v==ZERO:return ZERO
 m=Matrix(k)
 return simplify((project(k,v)+sign*I*m.cross(v)/norm[k])/2)

outputs={}
comm_total=S.Zero
product_total=S.Zero
for k in sorted(active):
 mixed=ZERO;comm=ZERO;product_rule=ZERO
 contributing=[]
 for p in sorted(active):
  q=sub(k,p)
  if q not in active:continue
  pp=hel(p,False,1);qm=hel(q,False,-1)
  fp=hel(p,True,1)
  if pp!=ZERO and qm!=ZERO:
   contributing.append([str(p),str(q)])
  mixed+=pp.cross(qm)
  comm+=fp.cross(qm)-hel(p,True,-1).cross(hel(q,False,1))
  product_rule+=fp.cross(qm)+pp.cross(hel(q,True,-1))
 mixed=simplify(mixed);comm=simplify(comm);product_rule=simplify(product_rule)
 work=simplify(2*expand(sum(conjugate(mixed[j])*comm[j] for j in range(3))).as_real_imag()[0])
 product_work=simplify(2*expand(sum(conjugate(mixed[j])*product_rule[j] for j in range(3))).as_real_imag()[0])
 if mixed!=ZERO or comm!=ZERO or work!=0:
  outputs[str(k)]={
   "mixed":cv(mixed),"commutator":cv(comm),"product_rule":cv(product_rule),
   "coherent_work":qstr(work),"product_rule_work":qstr(product_work),
   "pairs":contributing,
  }
 comm_total+=work;product_total+=product_work

mode_rows={}
prod=S.Zero;diss=S.Zero
for k in sorted(active):
 v=u.get(k,ZERO);f=force(k)
 hp=hel(k,False,1);hm=hel(k,False,-1)
 fp=hel(k,True,1);fm=hel(k,True,-1)
 p=S.Zero;d=S.Zero
 if v!=ZERO:
  p=simplify(2*weight(k)*expand(sum(conjugate(v[j])*f[j] for j in range(3))).as_real_imag()[0])
  d=simplify(weight(k)*sum(z*z for z in k)*sum(conjugate(v[j])*v[j] for j in range(3)))
  prod+=p;diss+=d
 if any(x!=ZERO for x in [v,f,hp,hm,fp,fm]):
  mode_rows[str(k)]={
   "norm":qstr(norm[k]),"weight":weight(k),
   "velocity":cv(v),"forcing":cv(f),
   "hplus_velocity":cv(hp),"hminus_velocity":cv(hm),
   "hplus_forcing":cv(fp),"hminus_forcing":cv(fm),
   "production_contribution":qstr(p),
   "dissipation_contribution":qstr(d),
  }

comm_total=simplify(comm_total);product_total=simplify(product_total)
prod=simplify(prod);diss=simplify(diss)
rate=simplify(6*(12*comm_total-prod+diss))
assert comm_total==Rational(-557627,125)
assert product_total==comm_total
assert prod==0
assert diss==15834
assert rate==Rational(-28273644,125)
# No hidden radicals are allowed in the finite certificate.
all_strings=json.dumps({"modes":mode_rows,"outputs":outputs})
assert "sqrt" not in all_strings
print(json.dumps({
 "schema":"ns_r829_rational_345_component_certificate_v1",
 "cube_radius":CUT,
 "mode_rows":mode_rows,
 "output_rows":outputs,
 "totals":{
  "coherent_work":qstr(comm_total),
  "product_rule_work":qstr(product_total),
  "critical_production":qstr(prod),
  "critical_dissipation":qstr(diss),
  "canonical_signed_rate":qstr(rate),
 },
 "all_emitted_active_values_rational":True,
 "repository_agda_reification_complete":False,
 "clay_promotion":False,
},indent=2))
