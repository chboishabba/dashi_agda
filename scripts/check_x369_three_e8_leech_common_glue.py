"""Exact shared sublattice and distinct glue for 3E8 and Golay Leech.

Reuse the concrete Golay parity/glue constructor and classical E8 = D8
union (D8 + half-ones), with exact integral coordinates / sqrt(8).
DASHI extension: explicit intersection via dual sum, HNF/SNF quotient
and bidirectional tagged gluing. No direct isometry between 3E8 and Leech.
"""
import argparse
from functools import lru_cache
from itertools import combinations, product
import json
from pathlib import Path

from sympy import Matrix, diag, ilcm, ZZ, Rational
from sympy.matrices.normalforms import hermite_normal_form, smith_normal_form
from scripts.check_x369_concrete_leech_golay_glue import basis, membership, require


def integer(a):
    require(all(x.q==1 for x in a),'nonintegral lattice inclusion')
    return a.applyfunc(int)


def vector(a):
    return tuple(map(int,integer(a)))


def matrix_rows(a):
    return [[int(x) for x in row] for row in integer(a).tolist()]


@lru_cache(maxsize=1)
def geometry():
    # M^T M = 8 I, so M sends standard E8 coordinates to our scaled
    # integer presentation without changing the normalized metric.
    m=diag(*([Matrix([[2,2],[2,-2]])]*4))
    require(m.T*m==8*Matrix.eye(8),'ambient scaled isometry failed')
    d8=Matrix([[int(j==i)-int(j==7) for j in range(8)]
                for i in range(7)]+[[2*int(j==7) for j in range(8)]]).T
    e8=hermite_normal_form(integer(m*d8.row_join(Matrix([1]*8)/2)))
    a=diag(e8,e8,e8)
    b=Matrix(basis())
    require(abs(a.det())==abs(b.det())==2**36,'ambient covolume mismatch')
    require((a.T*a/8).det()==1 and (b.T*b/8).det()==1,
            'normalized Gram covolume mismatch')
    # (A cap B)^* = A^* + B^*. Use integer HNF after clearing all
    # denominators, then invert transpose to recover the intersection.
    dual=a.inv().T.row_join(b.inv().T)
    d=ilcm(*[v.q for v in dual])
    dual_scaled=hermite_normal_form(integer(d*dual))
    common=hermite_normal_form(integer(d*dual_scaled.inv().T))
    require(abs(common.det())==2**48,'unexpected common sublattice index')
    sides={}
    for name,x in (('three_e8',a),('golay_leech',b)):
        inv=x.inv()
        inclusion=integer(inv*common)
        h=hermite_normal_form(inclusion)
        snf=smith_normal_form(inclusion,domain=ZZ)
        factors=tuple(abs(int(snf[i,i])) for i in range(24))
        require(factors==(1,)*12+(2,)*12,'unexpected glue group')
        require(abs(inclusion.det())==4096 and all(h[i,i]>0 for i in range(24)),
                'glue index mismatch')
        require(integer(inclusion.inv()*h).det() in (-1,1),
                'quotient HNF changes common sublattice')
        sides[name]=(x,inv,h,factors)
    return m,common,common.inv(),sides


def split(point,side):
    _,common,ci,sides=geometry()
    require(side in sides,'unknown glue side')
    x,xi,h,_=sides[side]
    point=tuple(point)
    require(len(point)==24 and all(type(v) is int for v in point),
            'integer ambient point required')
    p=Matrix(point);r=integer(xi*p)
    for j in reversed(range(24)):
        q=int(r[j])//int(h[j,j])
        r-=q*h[:,j]
    require(all(0<=r[i]<h[i,i] for i in range(24)),'invalid quotient remainder')
    c=integer(ci*(p-x*r))
    require(common*c+x*r==p,'glue split failed')
    return vector(c),vector(r)


def stitch(common_coordinates,residue,side):
    _,common,_,sides=geometry()
    require(side in sides,'unknown glue side')
    x,_,h,_=sides[side]
    c=tuple(common_coordinates);r=tuple(residue)
    require(len(c)==len(r)==24 and all(type(v) is int for v in c+r)
            and all(0<=r[i]<h[i,i] for i in range(24)),
            'invalid common or quotient coordinates')
    p=vector(common*Matrix(c)+x*Matrix(r))
    require(split(p,side)==(c,r),'glue inverse failed')
    return p


def e8_roots():
    for i,j in combinations(range(8),2):
        for a,b in product((-1,1),repeat=2):
            r=[0]*8;r[i]=a;r[j]=b
            yield Matrix(r)
    for signs in product((-1,1),repeat=8):
        if sum(x<0 for x in signs)%2==0:
            yield Matrix([Rational(x,2) for x in signs])


def certificate(enumerate_glue=False):
    m,common,ci,sides=geometry()
    counts={}
    for name,(x,xi,h,factors) in sides.items():
        for j in range(24):
            p=vector(x[:,j]);c,r=split(p,name)
            require(stitch(c,r,name)==p,'basis BIDI failed')
        other=sides['golay_leech' if name=='three_e8' else 'three_e8'][1]
        count=0
        if enumerate_glue:
            for r in product(*(range(int(h[j,j])) for j in range(24))):
                p=stitch((0,)*24,r,name)
                # Quotient exponent two, and a nonzero representative
                # belongs only to this side, by the exact intersection.
                integer(ci*(2*Matrix(p)))
                other_member=all(v.q==1 for v in other*Matrix(p))
                require(other_member==(not any(r)),'glue overlap outside intersection')
                count+=1
            require(count==4096,'glue enumeration count mismatch')
        counts[name]=dict(basis=matrix_rows(x),quotient_hnf=matrix_rows(h),
                          smith_factors=list(factors),index=4096,
                          enumerated_representatives=count)
    roots=set()
    for root in e8_roots():
        z=vector(m*root)
        require(sum(v*v for v in z)==16,'E8 root norm mismatch')
        for k in range(3):
            p=(0,)*(8*k)+z+(0,)*(8*(2-k))
            require(membership(p) is None,'E8 root incorrectly in Leech')
            split(p,'three_e8')
            roots.add(p)
    require(len(roots)==720,'E8 root count mismatch')
    return dict(
        status='concrete_common_sublattice_and_distinct_glues',
        ambient_alignment=matrix_rows(m),common_integer_basis=matrix_rows(common),
        common_integer_determinant=abs(int(common.det())),
        each_overlattice_integer_determinant=2**36,
        each_glue_group='(Z/2)^12',glue_sides=counts,
        all_720_three_e8_roots_excluded_from_leech=True,
        direct_three_e8_leech_isometry=False,
        same_neural_source_lattice_membership=False,
        full_conway_group_certified=False,agda_kernel_checked=False)


def main():
    p=argparse.ArgumentParser()
    p.add_argument('--enumerate-glue',action='store_true')
    p.add_argument('--output',type=Path)
    a=p.parse_args()
    result=json.dumps(certificate(a.enumerate_glue),sort_keys=True,indent=2)+'\n'
    if a.output:
        a.output.write_text(result)
    print(result,end='')


if __name__=='__main__':
    main()
