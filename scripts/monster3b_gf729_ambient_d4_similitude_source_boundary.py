#!/usr/bin/env python3
"""Ambient, NOT 2.Suz:2 source-group-verified, GF729 D4/GSp Heisenberg witness.

Reuses PR #1098 source-owner selected GF729 modulus and gamma. Original
ATLAS 2.Suz:2 matrix hashes are retained in PR #1098 source manifest.
NEW Frobenius^3 is an ambient GL6 element; it is NOT represented as an
ATLAS subgroup word or actual 3B Monster normalizer involution.

R=(multiplication by gamma^182, contragredient), order4; R²=-I12.
M=(Frobenius^3, negative contragredient), order2; multiplier -1.
MRM=R^-1 and both act by honest Heisenberg automorphisms with quadratic
central correction. Exact finite verification, no GAP or mmgroup needed.
"""
import json
from itertools import product

P=3
N=6
MODULUS=(1,0,0,0,1,1,1)
GAMMA=(0,1,0,1,1,0)
ZERO=(0,)*N
ONE=(1,0,0,0,0,0)

def fmul(a,b):
    c=[0]*11
    for i in range(N):
        for j in range(N):c[i+j]+=a[i]*b[j]
    for k in range(10,5,-1):
        t=c[k]%P
        for j in range(N):c[k-6+j]-=t*MODULUS[j]
    return tuple(z%P for z in c[:N])

def fpow(a,n):
    x=ONE
    while n:
        if n&1:x=fmul(x,a)
        a=fmul(a,a)
        n//=2
    return x

def matrix(f):
    cols=[f(tuple(int(j==k) for j in range(N))) for k in range(N)]
    return [[cols[k][j] for k in range(N)] for j in range(N)]

def mul(A,B):
    return [[sum(x*y for x,y in zip(row,col))%P for col in zip(*B)]
            for row in A]
def tr(A):return list(map(list,zip(*A)))
def ident(n):return [[int(i==j) for j in range(n)] for i in range(n)]
def minus(A):return [[(-x)%P for x in row] for row in A]
def blk(A,B):
    Z=[[0]*N for _ in range(N)]
    return [x+y for x,y in zip(A,Z)]+[x+y for x,y in zip(Z,B)]
def mv(A,v):return tuple(sum(x*y for x,y in zip(row,v))%P for row in A)
def dot(a,b):return sum(x*y for x,y in zip(a,b))%P
def plus(a,b):return tuple((x+y)%P for x,y in zip(a,b))
def hmul(x,y):
    a,b,c=x;aa,bb,d=y
    return plus(a,aa),plus(b,bb),(c+d+dot(b,aa))%P
def lift(A,chi,state):
    a,b,c=state
    image=mv(A,a+b)
    aa,bb=image[:N],image[N:]
    # Symmetrizing coboundary t=c+a·b in characteristic three.
    return aa,bb,(chi*(c+dot(a,b))-dot(aa,bb))%P

def audit():
    assert fpow(GAMMA,728)==ONE
    assert all(fpow(GAMMA,728//q)!=ONE for q in (2,7,13))
    root=fpow(GAMMA,182)
    assert fpow(root,4)==ONE
    assert fpow(root,2)==(2,0,0,0,0,0)
    A=matrix(lambda x:fmul(root,x))
    Ai=matrix(lambda x:fmul(fpow(root,3),x))
    F=matrix(lambda x:fpow(x,27))
    I6=ident(N)
    assert mul(A,Ai)==I6==mul(Ai,A)
    assert mul(F,F)==I6
    assert mul(mul(F,A),F)==Ai
    R=blk(A,tr(Ai))
    Rinv=blk(Ai,tr(A))
    M=blk(F,minus(tr(F)))
    I=ident(12)
    J=[[0]*12 for _ in range(12)]
    for k in range(6):J[k][6+k]=1;J[6+k][k]=2
    assert mul(mul(tr(R),J),R)==J
    assert mul(mul(tr(M),J),M)==minus(J)
    assert mul(R,R)==minus(I)
    assert mul(M,M)==I
    assert mul(mul(M,R),M)==Rinv
    generators=[(ZERO,ZERO,1)]
    for k in range(N):
        e=tuple(int(k==j) for j in range(N))
        generators.extend(((e,ZERO,0),(ZERO,e,0)))
    tested=0
    # 3^7 representative states x all 13 Heisenberg generators and 2 D4
    # generators. This does NOT exhaust all 3^13 Heisenberg states.
    for a in product(range(3),repeat=3):
        for b in product(range(3),repeat=3):
            stateA=tuple(a)+(0,)*3
            stateB=tuple(b)+(0,)*3
            for c in range(3):
                state=(stateA,stateB,c)
                for G,chi in ((R,1),(M,2)):
                    for h in generators:
                        assert lift(G,chi,hmul(state,h))==hmul(
                            lift(G,chi,state),lift(G,chi,h))
                        tested+=1
    assert tested==3**7*2*13
    return {'schema':'monster3b-ambient-gf729-d4-heisenberg-v1',
        'source_original_ATLAS':'PR #1098 vendored ATLAS 2.Suz GF3 and selected GF729 chart',
        'source_modulus_low_to_high':MODULUS,
        'source_primitive_root_coordinates':GAMMA,
        'source_primitive_order':728,
        'ambient_Frobenius_exponent':27,
        'ambient_field_rotation_power':182,
        'D4_order_four_rotation':True,
        'D4_rotation_square_is_minus_identity_12':True,
        'D4_order_two_mirror':True,
        'centre_multiplier_rotation':1,
        'centre_multiplier_reflection':2,
        'D4_relation_mrm_equals_r_inverse':True,
        'symplectic_dimension':12,
        'Heisenberg_generator_product_checks':tested,
        'actual_ATLAS_2Suz_outer_involution_word_produced':False,
        'actual_Monster_3B_group_embedding_produced':False,
        'physical_model_identification':False}
if __name__=='__main__':print(json.dumps(audit(),indent=2,sort_keys=True))
