#!/usr/bin/env python3
"""Exact 728-mode physical real-helical Fourier seed evaluation.

Uses the actual Leray projector P_k, positive sqrt(k dot k) helical
normalization and the literal truncated Galerkin RHS. Sparse execution
is exact because velocity and quadratic-forcing supports are enumerated.
This is an independently executable source computation, NOT a kernel receipt.
"""
from functools import lru_cache
from itertools import product
import json
from sympy import I, Matrix, Rational as Q, S, conjugate, expand, simplify, sqrt

CUT=4
MODES=set(product(range(-CUT,CUT+1),repeat=3))-{(0,0,0)}
ZERO=Matrix([0,0,0])
PLUS={(3,0,0): Matrix([0,2+2*I,-2-I]),
      (0,4,0): Matrix([2+2*I,0,2+2*I]),
      (3,4,0): Matrix([6*I,-Q(9,2)*I,-2+2*I])}
def neg(k): return tuple(-x for x in k)
def add(p,q): return tuple(a+b for a,b in zip(p,q))
def sub(p,q): return tuple(a-b for a,b in zip(p,q))
u={**PLUS,**{neg(k):v.applyfunc(conjugate) for k,v in PLUS.items()}}
assert len(u)==6
assert all(Matrix(k).dot(v)==0 for k,v in u.items())
assert all(u[neg(k)]==v.applyfunc(conjugate) for k,v in u.items())
def project(k,v):
    if k==(0,0,0): return ZERO
    m=Matrix(k)
    return simplify(v-m*(m.dot(v)/m.dot(m)))
@lru_cache(None)
def force(k):
    if k not in MODES: return ZERO
    raw=ZERO
    for p,up in u.items():
        q=sub(k,p)
        if q in u: raw+=up.dot(Matrix(q))*u[q]
    return simplify(-I*project(k,raw))
def velocity(k): return u.get(k,ZERO)
@lru_cache(None)
def helical(k,kind,sign):
    v=velocity(k) if kind=="u" else force(k)
    if v==ZERO: return ZERO
    m=Matrix(k)
    return simplify((project(k,v)+sign*I*m.cross(v)/sqrt(m.dot(m)))/2)
def rhs(k):
    if k not in MODES: return ZERO
    m=Matrix(k)
    return simplify(force(k)-m.dot(m)*velocity(k))
forcing_support={k for p in u for q in u
                 if (k:=add(p,q)) in MODES and force(k)!=ZERO}
mixed_outputs={k for p in u for q in u if (k:=add(p,q)) in MODES}
works={}
for k in sorted(mixed_outputs):
    mixed=ZERO
    comm=ZERO
    for p in u:
        q=sub(k,p)
        if q in u:
            mixed+=helical(p,"u",1).cross(helical(q,"u",-1))
    for p in forcing_support:
        q=sub(k,p)
        if q in u:
            comm+=(helical(p,"f",1).cross(helical(q,"u",-1))
                   -helical(p,"f",-1).cross(helical(q,"u",1)))
    mixed=simplify(mixed)
    comm=simplify(comm)
    work=simplify(2*expand(sum(conjugate(mixed[j])*comm[j]
                               for j in range(3))).as_real_imag()[0])
    if mixed!=ZERO or comm!=ZERO or work!=0: works[k]=work
weight=lambda k:2**((max(map(abs,k))-1).bit_length())
production=simplify(sum(
    2*weight(k)*expand(sum(conjugate(v[j])*force(k)[j]
                           for j in range(3))).as_real_imag()[0]
    for k,v in u.items()))
dissipation=simplify(sum(
    weight(k)*sum(t*t for t in k)*
    sum(conjugate(v[j])*v[j] for j in range(3))
    for k,v in u.items()))
coherent=simplify(sum(works.values(),S.Zero))
rate=simplify(6*(12*coherent-production+dissipation))
expected={(-3,-4,0):Q(-48),(-3,0,0):Q(322917,250),
          (-3,4,0):Q(-48),(0,-4,0):Q(-428272,125),
          (0,4,0):Q(-428272,125),(3,-4,0):Q(-48),
          (3,0,0):Q(322917,250),(3,4,0):Q(-48)}
assert works==expected,(works,expected)
assert coherent==Q(-557627,125)
assert production==0
assert dissipation==15834
assert rate==Q(-28273644,125)
assert all(Matrix(k).dot(rhs(k))==0 for k in MODES if rhs(k)!=ZERO)
assert all(rhs(neg(k))==rhs(k).applyfunc(conjugate)
           for k in MODES if rhs(k)!=ZERO)
print(json.dumps({
 "schema":"ns_real_full_helical_seed_v1",
 "cutoff_nonzero_modes":len(MODES),
 "selected_output_work":{str(k):str(v) for k,v in works.items()},
 "physical_helical_norms_genuine_sqrt":True,
 "coherent_work":str(coherent),
 "critical_production":str(production),
 "critical_dissipation":str(dissipation),
 "selected_signed_rate":str(rate),
 "physical_rhs_divergence_free":True,
 "physical_rhs_real":True,
 "full_real_trajectory_formalized":False,
 "R823_real_source_equality_kernel_checked":False,
 "Clay_promotion":False},indent=2))
