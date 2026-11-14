#!/usr/bin/env python3
"""ATLAS 2.Suz:2 source-word D4 has a 4E symplectic submodule (dim 8).

Primary matrices and Suzuki generator names: ATLAS/AtlasRep.
Prior repository owner: #1098 source D4 word and invariant alternating J12.
Classical mathematics: Maschke/finite character theory; char3 does not
divide |D4|. This NEW finite submodule is not geometric IIT JFine D4,
not selected Monster H/D_i, and not an actual 6.Suz 78 Hom intertwiner.
"""
from itertools import combinations, product
from pathlib import Path
import argparse
import json
from monster3b_atlas_actual_d4_word_witness import (
    audit as source_audit, W_ORDER10, CONJUGATOR, inverse_word,
    form, evaluate, trans, rectangular_rank_mod3,
)
from monster3b_atlas_source_word_order_d4_gate import (
    parse_meataxe, mm, ident, neg, power,
)

def mtx(n,k): return [[0]*k for _ in range(n)]
def eye(n): return [[int(i==j) for j in range(n)] for i in range(n)]
def col(m): return [list(v) for v in zip(*m)]
def fromcol(v): return [list(x) for x in zip(*v)]
def mul(a,b):
    return [[sum(u*v for u,v in zip(row,column))%3 for column in zip(*b)] for row in a]
def add(a,b):
    return [[(u+v)%3 for u,v in zip(row,other)] for row,other in zip(a,b)]
def scale(k,a):
    return [[k*x%3 for x in row] for row in a]
def rank(a): return rectangular_rank_mod3(a)
def rref(a):
    a=[row[:] for row in a]
    h=0;pivots=[]
    for j in range(len(a[0])):
        k=next((i for i in range(h,len(a)) if a[i][j]),None)
        if k is None: continue
        a[h],a[k]=a[k],a[h]
        if a[h][j]==2:a[h]=[2*x%3 for x in a[h]]
        for i in range(len(a)):
            if i!=h and a[i][j]:
                c=a[i][j]
                a[i]=[(x-c*y)%3 for x,y in zip(a[i],a[h])]
        pivots.append(j);h+=1
        if h==len(a):break
    return a,pivots
def inverse(a):
    n=len(a);b,p=rref([x+y for x,y in zip(a,eye(n))])
    assert p[:n]==list(range(n))
    return [row[n:] for row in b]
def nullspace(a):
    b,p=rref(a);n=len(a[0])
    ans=[]
    for j in range(n):
        if j in p:continue
        v=[0]*n;v[j]=1
        for i,k in enumerate(p):v[k]=-b[i][j]%3
        ans.append(v)
    return ans
def dot(a,b):return sum(x*y for x,y in zip(a,b))%3
def plus(a,b):return tuple((x+y)%3 for x,y in zip(a,b))
def heis(x,y):
    a,b,c=x;aa,bb,cc=y
    return plus(a,aa),plus(b,bb),(c+cc+dot(b,aa))%3
def act(T,chi,x):
    a,b,c=x
    out=tuple(dot(row,a+b) for row in T)
    aa,bb=out[:4],out[4:]
    return aa,bb,(chi*(c+dot(a,b))-dot(aa,bb))%3
def main(root):
    donor=source_audit(root)
    data=root/"data"/"atlas"
    C=parse_meataxe(data/"2Suzd2G1-f3r12aB0.m1")
    D=parse_meataxe(data/"2Suzd2G1-f3r12aB0.m2")
    J=form();I=ident()
    W=evaluate(W_ORDER10,C,D)
    M=power(W,5)
    g=evaluate(CONJUGATOR,C,D)
    gi=evaluate(inverse_word(CONJUGATOR),C,D)
    R=mm(M,mm(mm(g,M),gi))
    assert mm(R,R)==neg(I) and mm(M,M)==I
    assert mm(mm(trans(R),J),R)==J
    assert mm(mm(trans(M),J),M)==neg(J)

    # The +1 eigenspace of M is six-dimensional and totally isotropic.
    # The symmetric nondegenerate form B(v,w)=J(v,Rw) on that space
    # makes 4E + 2E an exact symplectic direct-sum decomposition.
    Pplus=scale(2,add(I,M))
    vectors=[]
    for v in col(Pplus):
        trial=vectors+[v]
        if rank(fromcol(trial))>len(vectors):vectors.append(v)
    assert len(vectors)==6
    Eplus=fromcol(vectors)
    assert mul(M,Eplus)==Eplus
    B=mul(mul(trans(Eplus),J),mul(R,Eplus))
    assert B==trans(B) and rank(B)==6
    choice=next(idx for idx in combinations(range(6),4)
                if rank([[B[i][j] for j in idx] for i in idx])==4)
    A=fromcol([vectors[j] for j in choice])
    B4=mul(mul(trans(A),J),mul(R,A))
    Q=inverse(B4)
    V=mul(mul(R,A),Q)
    X=[a+v for a,v in zip(A,V)]
    J8=[row+[int(i==j) for j in range(4)]
        for i,row in enumerate(mtx(4,4))]
    J8 += [[2*int(i==j)%3 for j in range(4)]+[0]*4
           for i in range(4)]
    Mr=[row+[0]*4 for row in eye(4)] + [
        [0]*4+row for row in scale(2,eye(4))]
    Rr=[[0]*4+row for row in scale(2,Q)] + [
        row+[0]*4 for row in B4]
    assert rank(X)==8 and mul(mul(trans(X),J),X)==J8
    assert mul(M,X)==mul(X,Mr) and mul(R,X)==mul(X,Rr)
    assert mul(Rr,Rr)==scale(2,eye(8))
    assert mul(Mr,Mr)==eye(8)
    assert mul(mul(Mr,Rr),Mr)==mul(Rr,mul(Rr,Rr))
    assert mul(mul(trans(Rr),J8),Rr)==J8
    assert mul(mul(trans(Mr),J8),Mr)==scale(2,J8)

    # Orthogonal complement is another actual D4-stable 2E summand.
    condition=mul(mul(trans(A),J),mul(R,Eplus))
    K=nullspace(condition)
    assert len(K)==2
    A2=mul(Eplus,fromcol(K))
    other=[a+b for a,b in zip(A2,mul(R,A2))]
    assert rank(other)==4
    assert rank([a+b for a,b in zip(X,other)])==12
    assert mul(mul(trans(X),J),other)==mtx(8,4)
    assert rank(mul(mul(trans(other),J),other))==4
    assert rank([a+b for a,b in zip(other,mul(M,other))])==4

    # Quadratic-corrected centre transport on a FOUR-pair H4.
    # It is sufficient to use c=0: the identities are affine in c.
    generators=[((0,)*4,(0,)*4,1)]
    for i in range(4):
        v=tuple(int(i==j) for j in range(4))
        generators += [(v,(0,)*4,0),((0,)*4,v,0)]
    checked=0
    for v in product(range(3),repeat=8):
        state=(v[:4],v[4:],0)
        for gen in generators:
            for T,chi in ((Rr,1),(Mr,2)):
                assert act(T,chi,heis(state,gen))==heis(
                    act(T,chi,state),act(T,chi,gen))
                checked+=1
    assert checked==118098
    return {
        "schema":"monster3b-ATLAS-4E-eight-dimensional-source-submodule-v1",
        "original_matrix_authority":"ATLAS/AtlasRep, 2.Suz:2 GF3 standard matrices",
        "donor_PR":1098,"source_D4_word_reflection":W_ORDER10+"^5",
        "source_D4_word_rotation":"m*(g*m*g^-1); g="+CONJUGATOR,
        "source_twelve_dim_irrep_character":"6E",
        "selected_irrep_indices":[int(j) for j in choice],
        "eight_dim_irrep_character":"4E",
        "four_dim_complement_irrep_character":"2E",
        "eight_dim_embedding_X_12_by_8":X,
        "restricted_rotation_R8":Rr,
        "restricted_reflection_M8":Mr,
        "restricted_alternating_form_J8":J8,
        "D4_intertwiners_and_symplectic_form_verified":True,
        "orthogonal_4D_source_complement_verified":True,
        "source_r_squared_on_all_twelve_is_negative_identity":True,
        "source_r_squared_on_eight_is_negative_identity":True,
        "H4_quadratic_central_lift_generator_checks":checked,
        "old_JFine_geometric_or_A2_model_equivariantly_identified":False,
        "selected_Monster_diagonal_H_over_Di_identified":False,
        "actual_Monster_6Suz_degree78_match":False,
        "actual_Monster_Wzeta_Hom_action":False,
        "agda_kernel_proved":False,
        "source_d4_receipt_donor_passed":donor["D4_presentation_verified"],
    }
if __name__=="__main__":
    cli=argparse.ArgumentParser()
    cli.add_argument("--receipt",type=Path)
    cli.add_argument("--root",type=Path,default=Path(__file__).resolve().parents[1])
    args=cli.parse_args()
    out=main(args.root);s=json.dumps(out,indent=2,sort_keys=True)+"\n"
    if args.receipt:args.receipt.write_text(s)
    print(s,end="")
