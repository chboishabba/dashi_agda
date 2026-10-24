#!/usr/bin/env python3
"""The source JFine eight-trit H4 steelman with Monster-necessary C4 character.

PRIOR OWNERS: IITJFineFourOneFourS3ZetaGaugeExact (raw 3x3/c-gauge);
TernaryMonsterSymmetryCandidateExact and D4IrrepFiniteFrickeEquivariantExact
(geometric D4 and oriented-sector types); Monster3BFiniteHeisenbergCentral-
ExtensionExact (standard H6/H4 cocycle). Original Monster class sources:
Barraclough--Wilson 2007, ATLAS, Breuer--Magaard--Wilson, and the independent
character-screen machinery in JFine/Monster PR #1250.

NEW MODEL (NOT GEOMETRIC AND NOT MONSTER-IDENTIFIED):
  V8' = A1 + A2 + 2 B1 + 2 B2 + E, centre multiplier A2.
  Turn one A1 to A2; split ONE previous E into B1+B2.
  D4 quarter stays in the phase-preserving C4; mirrors invert the centre.
  Necessary phase trace on C4: (65610,18,1458,18).
No new site/trit/Monster group operation is assumed or inferred.
"""
from __future__ import annotations
from itertools import product as tuples
import json
import iit_jfine_d4_single_line_orientation_bypass as old

P=3
mm=old.mm
tr=old.tr
eye=old.eye
rank=old.rank
R=[row[:] for row in old.R]
M=[row[:] for row in old.M0]
# Original 8 character co-ordinates: tE,tC,bE,bC,XE,YE,XC,YC.
# A1 -> A2 in tC (mirror sign only); one E -> B1+B2 in corner
# (quarter matrix -I, mirror unchanged).
assert M[1][1]==1
M[1][1]=2
R[6][6]=2; R[6][7]=0;R[7][6]=0;R[7][7]=2
OMEGA=[[0]*8 for _ in range(8)]
for i,j in ((0,1),(2,3),(6,7),(4,5)):
    OMEGA[i][j]=1;OMEGA[j][i]=2
Z=(0,0,0,0)

def mv(A,v):return tuple(sum(a*b for a,b in zip(row,v))%P for row in A)
def add(a,b):return tuple((x+y)%P for x,y in zip(a,b))
def dot(a,b):return sum(x*y for x,y in zip(a,b))%P
def to_h4(v,c):
    te,tc,be,bc,xe,ye,xc,yc=v
    return (tc,bc,yc,ye),(te,be,xc,xe),c
def from_h4(a,b,c):
    return (b[0],a[0],b[1],a[1],b[3],a[3],b[2],a[2]),c
def mul(v,c,w,d):
    a,b,cc=to_h4(v,c);aa,bb,dd=to_h4(w,d)
    return from_h4(add(a,aa),add(b,bb),(cc+dd+dot(b,aa))%P)
def act(g,chi,v,c):
    a,b,cc=to_h4(v,c)
    w=mv(g,v)
    aa,bb,_=to_h4(w,c)
    # t=c+a.b transforms by the symplectic similitude multiplier chi.
    # In char3, this symmetrises the standard b.a' cocycle.
    return w,(chi*(cc+dot(a,b))-dot(aa,bb))%P
def repeat(g,chi,v,c,n):
    for _ in range(n):v,c=act(g,chi,v,c)
    return v,c
def kernel_dimension(g,sgn=1):
    return 8-rank([[(g[i][j]-sgn*int(i==j))%P
                    for j in range(8)] for i in range(8)])

def audit():
    I=eye(8)
    assert mm(mm(mm(R,R),R),R)==I
    assert mm(M,M)==I and mm(mm(M,R),M)==mm(mm(R,R),R)
    assert mm(mm(tr(R),OMEGA),R)==OMEGA
    assert mm(mm(tr(M),OMEGA),M)==[[(-v)%3 for v in row] for row in OMEGA]
    assert rank(OMEGA)==8
    qrdef=[[(R[i][j]-old.R[i][j])%P for j in range(8)] for i in range(8)]
    mirdef=[[(M[i][j]-old.M0[i][j])%P for j in range(8)] for i in range(8)]
    assert rank(qrdef)==2 and rank(mirdef)==1
    gens=[from_h4(Z,Z,1)]
    for i in range(4):
        e=tuple(int(i==j) for j in range(4))
        gens.extend((from_h4(e,Z,0),from_h4(Z,e,0)))
    checks=relations=0
    for state in tuples(range(P),repeat=9):
        v=state[:8];c=state[8]
        assert from_h4(*to_h4(v,c))==(v,c)
        assert repeat(R,1,v,c,4)==(v,c)
        assert repeat(M,2,v,c,2)==(v,c)
        w,d=act(M,2,v,c);w,d=act(R,1,w,d);w,d=act(M,2,w,d)
        assert (w,d)==repeat(R,1,v,c,3)
        relations+=3
        for s,k in gens:
            for g,chi in ((R,1),(M,2)):
                assert act(g,chi,*mul(v,c,s,k))==mul(*act(g,chi,v,c),
                                                     *act(g,chi,s,k))
                checks+=1
    assert checks==354294 and relations==59049
    r2=mm(R,R);r3=mm(r2,R)
    assert kernel_dimension(R)==2 and kernel_dimension(r2)==6
    assert kernel_dimension(r3)==2
    # The original pointed 10-marker geometry has TWO fixed markers under
    # either quarter or half turn. The centre is fixed by rotations only.
    c4={'identity':10*3**8,'r':2*3**kernel_dimension(R),
        'r2':2*3**kernel_dimension(r2),'r3':2*3**kernel_dimension(r3)}
    assert c4=={'identity':65610,'r':18,'r2':1458,'r3':18}
    m={'one':(65610+1458+36)//4,'minus_one':(65610+1458-36)//4,
       'i':(65610-1458)//4,'minus_i':(65610-1458)//4}
    assert m=={'one':16776,'minus_one':16758,'i':16038,'minus_i':16038}
    return {'schema':'jfine-d4-oriented-c4-phase-steelman-v1',
       'changed_source_representation':'A1 + A2 + 2 B1 + 2 B2 + E',
       'original_geometric_D4_action_preserved':False,
       'original_19683_pointed_source_trits_retained':True,
       'new_trits':0,'quarter_operator_delta_rank':rank(qrdef),
       'mirror_operator_delta_rank':rank(mirdef),
       'D4_centre_multiplier_quarter':1,'D4_centre_multiplier_mirror':2,
       'nondegenerate_similitude_form_rank':rank(OMEGA),
       'H4_group_order':3**9,'H4_centre_order':3,
       'D4_H4_generator_product_checks':checks,'D4_group_relations_checks':relations,
       'zeta_phase_preserving_C4_character':c4,
       'C4_complex_character_sector_multiplicities':m,
       'necessary_3B_C4_character_match':True,
       'character_match_is_sufficient_for_subgroup':False,
       'actual_Monster_3B_D4_embedding_identified':False,
       'actual_6Suz_78_source_character_selected':False,
       'agda_kernel_checked':False}

if __name__=='__main__':print(json.dumps(audit(),sort_keys=True,indent=2))
