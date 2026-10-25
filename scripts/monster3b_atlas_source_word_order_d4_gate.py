#!/usr/bin/env python3
"""ATLAS source-word ORDER and Jordan discriminators, not Monster class fusions.

Reuses PR #1098 manifest-pinned ATLAS 2.Suz:2 MeatAxe generator bytes and
selected Heisenberg lift output. Original matrices: ATLAS/AtlasRep; repository
selected field/word computations remain credited to prior DASHI owners.

The selected outer generator has multiplier -1 but is NOT involutive.
An ambient GF729 Frobenius^3 mirror exists separately; it is not thereby
an element word in the original Atlas 2.Suz:2 group.
"""
from pathlib import Path
import json

N=12
def ident():return [[int(i==j) for j in range(N)] for i in range(N)]
def neg(A):return [[(-a)%3 for a in row] for row in A]
def mm(A,B):
    return [[sum(x*y for x,y in zip(row,col))%3 for col in zip(*B)] for row in A]
def diff(A,B):return [[(a-b)%3 for a,b in zip(row,other)] for row,other in zip(A,B)]
def rank(A):
    A=[row[:] for row in A]
    r=0
    for col in range(N):
        p=next((j for j in range(r,N) if A[j][col]),None)
        if p is None:continue
        A[p],A[r]=A[r],A[p]
        factor=1 if A[r][col]==1 else 2
        A[r]=[factor*x%3 for x in A[r]]
        for j in range(N):
            if j!=r and A[j][col]:
                q=A[j][col]
                A[j]=[(x-q*y)%3 for x,y in zip(A[j],A[r])]
        r+=1
        if r==N:break
    return r
def parse_meataxe(path):
    lines=[line.strip() for line in path.read_text().splitlines() if line.strip()]
    if len(lines)<13 or [int(s) for s in lines[0].split()]!=[1,3,12,12]:
        raise ValueError('not original 12x12 GF3 MeatAxe source')
    rows=lines[1:]
    if len(rows)!=12 or any(len(s)!=12 or not set(s)<=set('012') for s in rows):
        raise ValueError('unexpected matrix bytes')
    return [[int(z) for z in row] for row in rows]
def power(A,k):
    B=ident()
    while k:
        if k&1:B=mm(B,A)
        A=mm(A,A)
        k//=2
    return B

def audit(root):
    data=root/'data'/'atlas'
    g1=parse_meataxe(data/'2Suzd2G1-f3r12aB0.m1')
    g2=parse_meataxe(data/'2Suzd2G1-f3r12aB0.m2')
    I=ident()
    assert mm(g1,g1)==neg(I) and power(g1,4)==I
    assert power(g2,3)==I and g2!=I
    source=json.loads((root/'outputs'/'monster3b_selected_heisenberg_lift_20261012.json').read_text())
    if source.get('selected_word')!='g2 g1 g2^-1 g1 g2^-1':
        raise ValueError('selected word receipt identity changed')
    M=source['selected_word_matrix']
    if len(M)!=N or any(len(row)!=N for row in M):
        raise ValueError('not exact original 12D selected word')
    assert power(M,3)==neg(I) and power(M,6)==I
    assert M!=I and mm(M,M)!=I
    Q=diff(mm(M,M),I)
    Q2=mm(Q,Q)
    assert rank(Q)==6 and rank(Q2)==2
    assert mm(Q2,Q)==[[0]*N for _ in range(N)]
    j3=rank(Q2)
    j2=rank(Q)-2*j3
    j1=N-3*j3-2*j2
    assert [j3,j2,j1]==[2,2,2]
    return {'schema':'monster3b-atlas-source-word-actual-order-gate-v1',
       'original_ATLAS_outer_g1_order':4,
       'original_ATLAS_outer_g1_square_central_negative_identity':True,
       'original_ATLAS_outer_g1_is_D4_order2_mirror':False,
       'original_ATLAS_outer_g2_order':3,
       'previously_selected_word_order':6,
       'previously_selected_word_cube_central_negative_identity':True,
       'previously_selected_word_is_D4_order4_rotation':False,
       'previously_selected_word_square_unipotent_Jordan_partition':[3,3,2,2,1,1],
       'selected_word_square_minus_I_rank':6,
       'selected_word_square_unipotent_nilpotent_square_rank':2,
       'actual_Monster_class_fusion_paid':False,
       'existence_of_any_other_ATLAS_mirror_involution_ruled_out':False,
       'ambient_field_GF729_mirror_group_membership_paid':False}
if __name__=='__main__':
    print(json.dumps(audit(Path(__file__).resolve().parents[1]),indent=2,sort_keys=True))
