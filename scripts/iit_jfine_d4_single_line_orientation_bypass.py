#!/usr/bin/env python3
"""Minimal rank-one D4 orientation-line bypass on the original 3x3 JFine sheet.

Source owner: IITJFineFourOneFourS3ZetaGaugeExact (nine-trit relative gauge).
Earlier D4 irrep/orientation: TernaryMonsterSymmetryCandidateExact and
D4IrrepFiniteFrickeEquivariantExact. Earlier H4/H6: IITJFineHeisenbergFourPair-
SubgroupExact / Monster3BFiniteHeisenbergCentralExtensionExact. These precede
this bypass; do not reattribute their group laws, irrep types or original data.

IMPORTANT: the modified reflection is not the source geometric D4 site
permutation. It is a rank-one character-line defect B2 -> B1. This gives
an H4-compatible DIFFERENT D4 action, not an actual Monster normalizer.
"""
from __future__ import annotations
from itertools import product as tuples
import json
import iit_jfine_d4_symplectic_obstruction_audit as source

P=3
mm=source.product
tr=source.transpose
eye=source.identity
rank=source.rank
T=source.T
TINV=mm(tr(T),[[int(i==j)*w for j in range(8)] for i,w in enumerate((1,1,1,1,2,2,1,1))])
R=mm(mm(T,source.R),TINV)
M0=mm(mm(T,source.M),TINV)
M=[row[:] for row in M0]
assert M[3][3]==2   # Original corner B2 flips under axis mirror.
M[3][3]=1           # Only new choice: make it B1, keeping quarter turn.
MRAW=mm(mm(TINV,M),T)
# Dual equally minimal bypass: move B1 -> B2 instead of B2 -> B1.
M_DUAL=[row[:] for row in M0]
assert M_DUAL[2][2]==1
M_DUAL[2][2]=2
MRAW_DUAL=mm(mm(TINV,M_DUAL),T)
PAIRS=((0,1),(2,3),(4,6),(5,7))
OMEGA=[[0]*8 for _ in range(8)]
for i,j in PAIRS: OMEGA[i][j]=1;OMEGA[j][i]=2
Z=(0,0,0,0)

def mv(A,v): return tuple(sum(a*b for a,b in zip(row,v))%P for row in A)
def add(x,y): return tuple((a+b)%P for a,b in zip(x,y))
def dot(x,y): return sum(a*b for a,b in zip(x,y))%P
def to_h4(v,c):
    te,tc,be,bc,xe,ye,xc,yc=v
    return (tc,bc,xc,yc),(te,be,xe,ye),c
def from_h4(a,b,c):
    return (b[0],a[0],b[1],a[1],b[2],b[3],a[2],a[3]),c
def mul(v,c,w,d):
    a,b,cc=to_h4(v,c);aa,bb,dd=to_h4(w,d)
    return from_h4(add(a,aa),add(b,bb),(cc+dd+dot(b,aa))%P)
def action(g,v,c):return mv(g,v),c
def kernel_dim(A,sign):
    return 8-rank([[(A[i][j]-sign*int(i==j))%P for j in range(8)] for i in range(8)])

def orbit_certificate(mirror=M):
    g=eye(8);fine=pointed=0;classes={}
    for k in range(4):
        for mirrored in (False,True):
            h=mm(g,mirror) if mirrored else g
            plus=kernel_dim(h,1);minus=kernel_dim(h,-1)
            marker=10 if (k==0 and not mirrored) else 4 if mirrored else 2
            # Value-S3 translations are fixed-point-free on centre; its
            # three reflections each fix one centre trit and -h shell.
            contribution=3*(3**plus+3**minus)
            fine+=contribution;pointed+=marker*contribution
            cls=('axis' if k%2==0 else 'diagonal') if mirrored else (
                'identity' if k==0 else 'half' if k==2 else 'quarter')
            character=marker*3**plus
            if cls in classes:assert classes[cls]==character
            classes[cls]=character
        g=mm(R,g)
    assert fine==25680 and pointed==219648
    assert tuple(classes[c] for c in ('identity','half','quarter','axis','diagonal'))==(65610,162,18,2916,324)
    return {'fine_joint_orbits':fine//48,'moving_marker_pointed_joint_orbits':pointed//48,
            'fine_burnside_numerator':fine,'pointed_burnside_numerator':pointed,
            'zeta_D4_phase_character':classes}

def audit():
    I=eye(8)
    assert mm(TINV,T)==mm(T,TINV)==I
    assert mm(mm(mm(R,R),R),R)==I
    assert mm(M,M)==I and mm(mm(M,R),M)==mm(mm(R,R),R)
    assert mm(mm(tr(R),OMEGA),R)==OMEGA
    assert mm(mm(tr(M),OMEGA),M)==OMEGA
    assert rank(OMEGA)==8
    defect=[[(MRAW[i][j]-source.M[i][j])%P for j in range(8)] for i in range(8)]
    assert rank(defect)==1
    dual_defect=[[(MRAW_DUAL[i][j]-source.M[i][j])%P for j in range(8)] for i in range(8)]
    assert rank(dual_defect)==1
    assert mm(M_DUAL,M_DUAL)==I
    assert mm(mm(M_DUAL,R),M_DUAL)==mm(mm(R,R),R)
    assert mm(mm(tr(M_DUAL),OMEGA),M_DUAL)==OMEGA
    checked=0
    for v in tuples(range(P),repeat=8):
        assert mv(TINV,mv(T,v))==v
        assert mv(TINV,mv(M,mv(T,v)))==mv(MRAW,v)
        for g in (R,M):
            a,b,_=to_h4(v,0); aa,bb,_=to_h4(mv(g,v),0)
            assert dot(a,b)==dot(aa,bb) # exact unsymmetrized cocycle
        checked+=1
    assert checked==6561
    gens=[from_h4(Z,Z,1)]
    for i in range(4):
        e=tuple(int(i==j) for j in range(4))
        gens.extend([from_h4(e,Z,0),from_h4(Z,e,0)])
    count=0
    for state in tuples(range(P),repeat=9):
        v=state[:8];c=state[8]
        assert from_h4(*to_h4(v,c))==(v,c)
        for g in (R,M):
            for w,d in gens:
                assert action(g,*mul(v,c,w,d))==mul(*action(g,v,c),*action(g,w,d))
                count+=1
    assert count==354294
    dual_count=0
    for state in tuples(range(P),repeat=9):
        v=state[:8];centre=state[8]
        for w,d in gens:
            assert action(M_DUAL,*mul(v,centre,w,d))==mul(*action(M_DUAL,v,centre),*action(M_DUAL,w,d))
            dual_count+=1
    assert dual_count==177147
    dual_orbit=orbit_certificate(M_DUAL)
    assert dual_orbit['fine_joint_orbits']==535
    assert dual_orbit['moving_marker_pointed_joint_orbits']==4576
    assert dual_orbit['zeta_D4_phase_character']=={
       'identity':65610,'half':162,'quarter':18,'axis':324,'diagonal':2916}
    return {'schema':'jfine-d4-single-line-orientation-bypass-v1',
      'source_sheet_states':19683,'relative_chart_roundtrips':checked,
      'new_trits':0,'source_geometric_reflection_preserved':False,
      'mirror_rank_one_operator_defect':rank(defect),
      'changed_irrep':'B2 -> B1 on one original corner contrast',
      'twisted_irrep_decomposition':'2 A1 + 2 B1 + 2 E',
      'twisted_symplectic_rank':rank(OMEGA),
      'twisted_D4_acts_by_H4_automorphisms':True,
      'H4_source_centre_fixed':True,
      'H4_order':3**9,'H4_centre_order':3,
      'H4_nontrivial_irrep_degree':81,
      'D4_original_source_group_action_checks':count,
      'complex_C3_phase_bulk_dimension_each':10*3**8,
      'actual_Monster_normalizer_same_object':False,
      'agda_kernel_proof_checked':False,**orbit_certificate()}

if __name__=='__main__':print(json.dumps(audit(),indent=2,sort_keys=True))
