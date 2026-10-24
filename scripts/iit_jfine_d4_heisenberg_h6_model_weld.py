#!/usr/bin/env python3
"""Explicit source-D4 repaired-form -> existing six-pair H6 MODEL symplectic weld.

Reuse IITJFineD4EquivariantHeisenbergGaugeExact and the source-D4
alternating-form audit. The D4 lift has a quadratic central correction,
so it is NOT the raw site D4 on the centre and is NOT the Monster action.
"""
import itertools
import json
import iit_jfine_d4_symplectic_obstruction_audit as x

PAIRS=((0,1),(2,3),(4,5),(6,8),(7,9),(10,11))
ZERO=(0,)*6

def to_standard(v):
    return tuple(v[j] for i,j in PAIRS),tuple(v[i] for i,j in PAIRS)
def from_standard(a,b):
    v=[0]*12
    for k,(i,j) in enumerate(PAIRS):v[i]=b[k];v[j]=a[k]
    return tuple(v)
def vecmat(m,v):
    return tuple(sum(a*b for a,b in zip(row,v))%3 for row in m)
def pair(v,w,o):
    return sum(v[i]*o[i][j]*w[j] for i in range(len(v)) for j in range(len(w)))%3
def plus(a,b):return tuple((i+j)%3 for i,j in zip(a,b))
def dot(a,b):return sum(i*j for i,j in zip(a,b))%3
def hprod(p,q):
    a,b,c=p;aa,bb,cc=q
    return plus(a,aa),plus(b,bb),(c+cc+dot(b,aa))%3
def lift(m,g):
    a,b,c=g;t=(c+dot(a,b))%3
    ap,bp=to_standard(vecmat(m,from_standard(a,b)))
    return ap,bp,(t-dot(ap,bp))%3

def audit():
    basis=[]
    for i in range(6):
        e=tuple(int(i==j) for j in range(6))
        basis.extend([(e,ZERO,0),(ZERO,e,0)])
    basis.append((ZERO,ZERO,1))
    for u in x.eye(12):
        a,b=to_standard(u)
        assert from_standard(a,b)==tuple(u)
    basis_pairs=0
    for u,v in itertools.product(x.eye(12),repeat=2):
        a,b=to_standard(u);aa,bb=to_standard(v)
        assert (dot(b,aa)-dot(bb,a))%3==pair(u,v,x.O12)
        basis_pairs+=1
    R,M=x.R12,x.M12
    assert x.mm(x.mm(x.mm(R,R),R),R)==x.eye(12)
    assert x.mm(M,M)==x.eye(12)
    assert x.mm(x.mm(M,R),M)==x.mm(x.mm(R,R),R)
    automorphism_checks=0
    for g in (R,M):
        for u,v in itertools.product(basis,repeat=2):
            assert lift(g,hprod(u,v))==hprod(lift(g,u),lift(g,v))
            automorphism_checks+=1
    # A is the actual source-eight-shell chart inclusion, not an abstract
    # cardinality mapping. The D4-stable group preimage has centre 3^(1+2).
    A=[row[:] for row in x.A]+[[0]*8 for _ in range(2)]
    assert x.rank(A)==8
    assert x.mm(R,A)==x.mm(A,x.R8)
    assert x.mm(M,A)==x.mm(A,x.M8)
    o=x.mm(x.mm(x.tr(A),x.O12),A)
    assert x.rank(o)==6
    assert 3**6+18*(3**3)**2==3**9
    assert 3**8+2*(3**4)**2==3**9
    return {
      "schema":"iit-jfine-d4-h6-model-weld-v1",
      "source":"PR #1148 source-edge-corner D4 quotient action",
      "repaired_H6_model_quotient_rank":12,
      "source_subspace_dimension":8,
      "source_subspace_commutator_rank":6,
      "source_subspace_group_order":19683,
      "source_subspace_centre_order":27,
      "source_subspace_model_type":"H3 x C3^2 (not extraspecial H4)",
      "H3_C3sq_linear_irreps":6561,
      "H3_C3sq_nonlinear_irreps":18,
      "H3_C3sq_nonlinear_irrep_degree":27,
      "chosen_H4_nonlinear_irreps":2,
      "chosen_H4_nonlinear_irrep_degree":81,
      "basis_pair_checks":basis_pairs,
      "D4_H6_generator_group_law_checks":automorphism_checks,
      "D4_lift_needs_central_quadratic_correction":True,
      "original_JFine_D4_centre_action_intertwined":False,
      "actual_Monster_normalizer_identified":False,
      "agda_kernel_checked":False}
if __name__=="__main__":print(json.dumps(audit(),indent=2,sort_keys=True))
