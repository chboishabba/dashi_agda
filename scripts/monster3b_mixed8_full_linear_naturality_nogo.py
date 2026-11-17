#!/usr/bin/env python3
"""Finite GF3/D4 commutator no-go for a full-linear-natural MIXED8 chart.

Uses the existing #1098 source-type E+E and #1250 MIXED8 action. Classical
group/representation theory, NOT Monster conjugacy, source-selected 6.Suz
character, actual Heisenberg Hom or IIT/phi same-object evidence.
"""
import json
from itertools import product

F = range(3)
I = ((1, 0), (0, 1))
MINUS_I = ((2, 0), (0, 2))
# Quaternion pair inside GL2(F3), on the E+E multiplicity index.
A = ((0, 2), (1, 0))
B = ((1, 1), (1, 2))


def mul(a, b):
    return tuple(tuple(sum(a[i][k] * b[k][j] for k in (0, 1)) % 3
                       for j in (0, 1)) for i in (0, 1))


def inverse(a):
    a00, a01 = a[0]
    a10, a11 = a[1]
    det = (a00 * a11 - a01 * a10) % 3
    if det == 0:
        raise ValueError("singular")
    dinv = pow(det, -1, 3)
    return (((a11*dinv) % 3, (-a01*dinv) % 3),
            ((-a10*dinv) % 3, (a00*dinv) % 3))


def commutator(a, b):
    return mul(mul(mul(a, b), inverse(a)), inverse(b))


def rotate(v):
    return tuple(z for x,y in zip(v[::2],v[1::2])
                 for z in ((-y)%3,x))


def mirror(v):
    return tuple(z for x,y in zip(v[::2],v[1::2])
                 for z in (x,(-y)%3))


def source_action(a, v):
    x,y,u,w = v
    return ((a[0][0]*x+a[0][1]*u)%3,
            (a[0][0]*y+a[0][1]*w)%3,
            (a[1][0]*x+a[1][1]*u)%3,
            (a[1][0]*y+a[1][1]*w)%3)


def kind(y):
    return "axis" if (y[0]==0)!=(y[1]==0) else "diagonal"


def target_auto(y, axis_sign, diagonal_sign):
    s = axis_sign if kind(y)=="axis" else diagonal_sign
    return tuple((s*x)%3 for x in y)


def certificate():
    assert mul(A,A)==mul(B,B)==MINUS_I
    assert mul(A,B)==mul(MINUS_I,mul(B,A))
    assert commutator(A,B)==MINUS_I
    assert mul(MINUS_I,MINUS_I)==I
    X=[v for v in product(F,repeat=4) if any(v)]
    Y=[y for y in product(F,repeat=2) if any(y)]
    GL2=[((a,b),(c,d)) for a,b,c,d in product(F,repeat=4)
         if (a*d-b*c)%3]
    assert len(GL2)==48 and len(X)==80 and len(Y)==8
    for g in GL2:
        assert all(source_action(g,rotate(v))==rotate(source_action(g,v))
                   and source_action(g,mirror(v))==mirror(source_action(g,v))
                   for v in X)
    for v in X:
        assert source_action(MINUS_I,v)==rotate(rotate(v))
    for y in Y:
        assert rotate(rotate(y))!=y
    for signs in product((1,2),repeat=2):
        assert len({target_auto(y,*signs) for y in Y})==8
        for y in Y:
            assert target_auto(rotate(y),*signs)==rotate(target_auto(y,*signs))
            assert target_auto(mirror(y),*signs)==mirror(target_auto(y,*signs))
    # Aut_D4(Y)=C2 x C2 is abelian. Every group homomorphism rho from
    # GL2(F3) kills commutators; therefore rho(-I)=id. But r^2=-I
    # on X and r^2=-I with no fixed points on Y. Consequently no
    # simultaneously D4- and rho(GL2)-equivariant f:X->Y exists.
    return {
      "schema":"monster3b-mixed8-full-linear-naturality-nogo-v1",
      "source_D4_centralizer":"GL2(F3)",
      "source_centralizer_order":len(GL2),
      "target_D4_centralizer":"C2 x C2",
      "target_centralizer_order":4,
      "commutator_A":A,"commutator_B":B,
      "commutator_AB":commutator(A,B),
      "commutator_equals_minus_identity":True,
      "source_minus_identity_is_D4_r_squared":True,
      "target_antipode_has_fixed_points":False,
      "full_linear_natural_D4_map_exists":False,
      "balanced_fibres_required_for_no_go":False,
      "selected_Monster_source_word":False,
      "actual_6Suz_degree78_selected":False,
      "Heisenberg_Hom_constructed":False,
      "IIT_observable_identified":False,
      "Agda_kernel_checked":False,
      "status":"EXACT_FINITE_CHART_NOGO_ONLY"
    }


if __name__=="__main__":
    print(json.dumps(certificate(),indent=2,sort_keys=True))
