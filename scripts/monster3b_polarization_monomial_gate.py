#!/usr/bin/env python3
"""Exact F3 NECESSARY test for a monomial/basis-label zeta square.

Uses #1098's selected original 12D AtlasRep symplectic action and stable
Lagrangian WHEN authenticated inputs are supplied. The merged #695
appraisal square is a selected basis-chart consumer, NOT automatically
a full Weil/Monster normalizer intertwiner. Nonpreserving operators
require Fourier/Weil basis mixing, not a point permutation.
No actual source matrices are authenticated by this module.
"""
import argparse
import json
from pathlib import Path

F=3

def shape(a):
    if not isinstance(a,list) or not a or not all(isinstance(r,list) for r in a):
        raise ValueError("nonempty rectangular matrix required")
    n=len(a[0])
    if n==0 or any(len(r)!=n or any(type(v) is not int for v in r) for r in a):
        raise ValueError("invalid matrix entries/shape")
    return len(a),n

def rank(matrix):
    a=[[v%F for v in row] for row in matrix]
    nr,nc=shape(a)
    k=0
    for col in range(nc):
        pivot=next((j for j in range(k,nr) if a[j][col]),None)
        if pivot is None:continue
        a[k],a[pivot]=a[pivot],a[k]
        inv=pow(a[k][col],-1,F)
        a[k]=[(v*inv)%F for v in a[k]]
        for j in range(nr):
            if j==k:continue
            scalar=a[j][col]
            if scalar:a[j]=[(v-scalar*w)%F for v,w in zip(a[j],a[k])]
        k+=1
        if k==nr:break
    return k

def multiply(a,b):
    n,k=shape(a)
    l,m=shape(b)
    if k!=l:raise ValueError("matrix multiplication shape mismatch")
    return [[sum(a[i][t]*b[t][j] for t in range(k))%3
             for j in range(m)] for i in range(n)]

def transpose(a):
    return [list(row) for row in zip(*a)]

def check(operator,lagrangian,form):
    n,nn=shape(operator)
    m,h=shape(lagrangian)
    if n!=nn or n!=m or n!=2*h:
        raise ValueError("operator 2h square and Lagrangian 2h by h required")
    if rank(lagrangian)!=h:raise ValueError("Lagrangian deficient rank")
    fn,fm=shape(form)
    if fn!=n or fm!=n or rank(form)!=n:
        raise ValueError("original nondegenerate alternating form required")
    if any((form[i][j]+form[j][i])%3 for i in range(n) for j in range(n)):
        raise ValueError("not skew symmetric")
    if any(form[i][i]%3 for i in range(n)):
        raise ValueError("not alternating")
    iso=multiply(multiply(transpose(lagrangian),form),lagrangian)
    if any(any(v for v in row) for row in iso):
        raise ValueError("selected halfspace not isotropic")
    formed=multiply(multiply(transpose(operator),form),operator)
    multipliers=[lam for lam in (1,2) if
        all(formed[i][j]==lam*form[i][j]%3
            for i in range(n) for j in range(n))]
    if len(multipliers)!=1:
        raise ValueError("not a symplectic similitude")
    transformed=[[sum(operator[i][j]*lagrangian[j][k]
                      for j in range(n))%3 for k in range(h)]
                 for i in range(n)]
    combined=[a+b for a,b in zip(lagrangian,transformed)]
    mixed=rank(combined)
    assert h<=mixed<=n
    return dict(schema="monster3b-polarization-basis-monomial-necessary-gate-v1",
        dimension=n,lagrangian_dimension=h,
        symplectic_multiplier=multipliers[0],
        span_original_and_transformed_rank=mixed,
        preserves_chosen_polarization=(mixed==h),
        simple_basis_permutation_not_ruled_out=(mixed==h),
        fourier_Weil_mixing_required_if_nonpreserving=(mixed>h),
        monomial_action_sufficiently_proved=False,
        source_ATLAS_input_authenticated_by_this_checker=False,
        actual_Monster_normalizer_Hom_constructed=False,
        status="EXACT_GF3_NECESSARY_GATE_ONLY")

if __name__=="__main__":
    p=argparse.ArgumentParser()
    p.add_argument("source_matrix_json",type=Path)
    args=p.parse_args()
    source=json.loads(args.source_matrix_json.read_text())
    print(json.dumps(check(source["operator"],source["lagrangian"],
                           source["alternating_form"]),indent=2,sort_keys=True))
