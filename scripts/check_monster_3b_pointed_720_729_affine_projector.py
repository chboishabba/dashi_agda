#!/usr/bin/env python3
"""Exact 720+9 -> 729 six-trit bridge and Heisenberg projector obstruction.

Original mathematics: Stone--von Neumann/finite Schrödinger modules,
Serre, Terras. Wilson (1988) and Barraclough--Wilson (2007) own the original
Monster 3B characters. Repository owners: Base369PointedAppraisalFibreExact,
Base369Pointed729NestedNinetyBidiExact, Monster3BFiniteSchrodingerPointProjectorExact,
Monster3BFiniteHeisenbergGeneratorsExact, Monster3BWilsonPublishedRestrictionReconciliationExact.
This is a CHOSEN basis codec, not an actual Monster intertwiner or Atlas D4 action.
"""
import argparse
import json
from itertools import product
from pathlib import Path

X = list(product(range(3), repeat=6))
ORIGIN = (0,)*6
def add(a,b): return tuple((x+y)%3 for x,y in zip(a,b))
def neg(a): return tuple((-x)%3 for x in a)
def dot(a,b): return sum(x*y for x,y in zip(a,b))%3
def integer(a): return sum(x*3**i for i,x in enumerate(a))
def trits(k): return tuple(k//3**i%3 for i in range(6))
def pointed_to_int(a):
    if a[0]=="central":
        assert 0<=a[1]<9
        return a[1]
    _,corner,fine,t=a
    assert 0<=corner<8 and 0<=fine<10 and 0<=t<9
    return 9*(1+10*corner+fine)+t
def int_to_pointed(k):
    assert 0<=k<729
    q,t=divmod(k,9)
    if q==0: return ("central",t)
    corner,fine=divmod(q-1,10)
    return ("noncentral",corner,fine,t)
def affine_label(x): return integer(x[2:])
def plane(x): return x[2:]==(0,0,0,0)
def Hprod(g,h):
    a,b,c=g;d,e,f=h
    return (add(a,d),add(b,e),(c+f+dot(b,d))%3)

def audit():
    assert len(X)==729
    addresses=[("central",t) for t in range(9)]+[
        ("noncentral",c,f,t) for c,f,t in product(range(8),range(10),range(9))]
    assert len(addresses)==729
    assert set(map(pointed_to_int,addresses))==set(range(729))
    assert all(int_to_pointed(pointed_to_int(a))==a for a in addresses)
    assert all(pointed_to_int(int_to_pointed(i))==i for i in range(729))
    cosets=[[x for x in X if affine_label(x)==q] for q in range(81)]
    assert all(len(c)==9 for c in cosets)
    assert len(set().union(*(set(c) for c in cosets)))==729
    assert all(not(set(cosets[i])&set(cosets[j]))
               for i in range(81) for j in range(i))
    translations_fixing=[a for a in X if all(plane(add(a,x)) for x in cosets[0])]
    assert len(translations_fixing)==9
    outside=next(a for a in X if not plane(a))
    assert not plane(add(outside,ORIGIN))
    orbit=set(tuple(sorted({affine_label(add(a,x)) for x in cosets[0]})) for a in X)
    assert len(orbit)==81
    # A modulation is diagonal, so commutes with every coordinate projector.
    # The subgroup preserving P0 has 9 translations, 729 modulations,
    # and 3 central phases; its Heisenberg commutator is NONTRIVIAL.
    a=(1,0,0,0,0,0);b=a
    gh=Hprod((a,ORIGIN,0),(ORIGIN,b,0))
    hg=Hprod((ORIGIN,b,0),(a,ORIGIN,0))
    assert gh[:2]==hg[:2] and (gh[2]-hg[2])%3==2
    horder=len(translations_fixing)*len(X)*3
    fullorder=len(X)*len(X)*3
    assert (horder,fullorder,fullorder//horder)==(19683,1594323,81)
    phase_hist=[]
    for b in X:
        counts=tuple(sum(dot(b,x)==j for x in cosets[0]) for j in range(3))
        assert counts in ((9,0,0),(3,3,3))
        phase_hist.append(counts)
    assert phase_hist.count((9,0,0))==81
    assert phase_hist.count((3,3,3))==648
    assert 720+9==729==720+8+1
    assert 720*90+8*90+90==728*90+90==65610
    assert 65520+143==65610+53==65663
    return dict(status="PASS_exact_affine_projector_model",
        pointed_addresses=729,rank9_fibre_count=81,noncentral_addresses=720,
        affine_projector_stabilizing_translations=9,
        affine_projector_moving_translations=720,
        affine_projector_conjugate_orbit=81,
        Heisenberg_projector_stabilizer_order=horder,
        full_Heisenberg6_order=fullorder,
        stabilizer_nonabelian_weyl_commutator=True,
        characteristic3_Eisenstein_lambda9_additive_group_isomorphic=False,
        modulation_histogram=dict(phase_constant=81,phase_balanced=648),
        rank9_projector_full_Heisenberg_invariant=False,
        explicit_moving_translation=outside,
        Wilson_65520_plus143_numerical_reconciliation=True,
        Wilson_143_representation_split_inferred=False,
        pointed_720_9_Monster_equivariant_intertwiner=False,
        actual_ATLAS_2Suz_D4_preservation_checked=False,
        Monster_source_78_selected=False,
        Agda_kernel_checked=False)
if __name__=="__main__":
    p=argparse.ArgumentParser()
    p.add_argument("--out",type=Path)
    a=p.parse_args()
    data=json.dumps(audit(),indent=2)+"\n"
    if a.out:a.out.write_text(data)
    print(data,end="")
