#!/usr/bin/env python3
"""Exact F3 D4-symplectic obstruction and minimal model repair.

Source operators: IITJFineFourOneFourS3ZetaGaugeExact.quarterSheet/mirrorSheet
and IITJFineD4EquivariantHeisenbergGaugeExact, PR #1148.
This constructs model actions, not an actual Monster normalizer action.
"""
import itertools
import json

def product(A,B):
    return [[sum(x*y for x,y in zip(row,col))%3 for col in zip(*B)] for row in A]

def transpose(A): return [list(row) for row in zip(*A)]
def identity(n): return [[int(i==j) for j in range(n)] for i in range(n)]
def diag(*parts):
    n=sum(map(len,parts)); A=[[0]*n for _ in range(n)]; p=0
    for part in parts:
        for i,row in enumerate(part):
            for j,x in enumerate(row): A[p+i][p+j]=x%3
        p+=len(part)
    return A
def permutation(indices):
    return [[int(j==indices[i]) for j in range(len(indices))] for i in range(len(indices))]
def rank(A):
    A=[row[:] for row in A]; k=0
    for j in range(len(A[0])):
        pivot=next((i for i in range(k,len(A)) if A[i][j]%3),None)
        if pivot is None: continue
        A[pivot],A[k]=A[k],A[pivot]
        s=pow(A[k][j],-1,3); A[k]=[(s*x)%3 for x in A[k]]
        for i in range(len(A)):
            if i!=k and A[i][j]:
                t=A[i][j]; A[i]=[(x-t*y)%3 for x,y in zip(A[i],A[k])]
        k+=1
        if k==len(A): break
    return k
def kernel(A,n):
    A=[row[:] for row in A]; pivots=[]; k=0
    for j in range(n):
        i=next((i for i in range(k,len(A)) if A[i][j]%3),None)
        if i is None: continue
        A[i],A[k]=A[k],A[i]
        s=pow(A[k][j],-1,3);A[k]=[(s*x)%3 for x in A[k]]
        for h in range(len(A)):
            if h!=k and A[h][j]:
                s=A[h][j];A[h]=[(x-s*y)%3 for x,y in zip(A[h],A[k])]
        pivots.append(j);k+=1
        if k==len(A): break
    basis=[]
    for free in range(n):
        if free in pivots: continue
        v=[0]*n;v[free]=1
        for i,j in enumerate(pivots):v[j]=-A[i][free]%3
        basis.append(v)
    return basis
R=diag(permutation([3,0,1,2]),permutation([2,0,3,1]))
M=diag(permutation([0,3,2,1]),permutation([1,0,3,2]))
pairs=list(itertools.combinations(range(8),2))
def skew(coeff):
    A=[[0]*8 for _ in range(8)]
    for (i,j),v in zip(pairs,coeff):A[i][j]=v%3;A[j][i]=-v%3
    return [[x%3 for x in row] for row in A]
def preserves(G,O,sgn=1):
    return product(product(transpose(G),O),G)==[[sgn*x%3 for x in row] for row in O]
def all_forms(rs,ms):
    constraints=[]
    for G,sign in [(R,rs),(M,ms)]:
        basis=[product(product(transpose(G),skew([int(l==k) for l in range(28)])),G) for k in range(28)]
        for i,j in pairs:
            constraints.append([(basis[k][i][j]-sign*int(pairs[k]==(i,j)))%3 for k in range(28)])
    K=kernel(constraints,28); hist={}
    for q in itertools.product(range(3),repeat=len(K)):
        v=[sum(c*b[j] for c,b in zip(q,K))%3 for j in range(28)]
        O=skew(v);assert preserves(R,O,rs) and preserves(M,O,ms)
        r=rank(O);hist[r]=hist.get(r,0)+1
    return {"dimension":len(K),"forms":3**len(K),"max_rank":max(hist),"rank_histogram":hist}
# D4 character coordinates in this order: tE,tC,bE,bC,XE,YE,XC,YC
T=[[1,1,1,1,0,0,0,0],
 [0,0,0,0,1,1,1,1],
 [1,-1,1,-1,0,0,0,0],
 [0,0,0,0,1,-1,-1,1],
 [1,0,-1,0,0,0,0,0],
 [0,1,0,-1,0,0,0,0],
 [0,0,0,0,1,1,-1,-1],
 [0,0,0,0,-1,1,-1,1]]
T=[[x%3 for x in row] for row in T]
# Insert two missing B1/B2 partners; the map is D4-equivariant.
J=[[0]*8 for _ in range(10)]
for i,j in enumerate([0,1,2,4,6,7,8,9]):J[j][i]=1
A=product(J,T);assert rank(A)==8
quarter=[[0,2],[1,0]]; mirror=[[1,0],[0,2]]
R10=diag(identity(2),[[2]],[[2]],[[2]],[[2]],quarter,quarter)
M10=diag(identity(2),[[1]],[[1]],[[2]],[[2]],mirror,mirror)
assert product(R10,A)==product(A,R) and product(M10,A)==product(A,M)
O10=[[0]*10 for _ in range(10)]
for i,j in [(0,1),(2,3),(4,5),(6,8),(7,9)]:O10[i][j]=1;O10[j][i]=2
assert rank(O10)==10 and preserves(R10,O10) and preserves(M10,O10)
O8=product(product(transpose(A),O10),A)
assert rank(O8)==6 and preserves(R,O8) and preserves(M,O8)
# Complete with a trivial symplectic pair, yielding the H6-sized 12D MODEL.
R12=diag(R10,identity(2));M12=diag(M10,identity(2))
O12=diag(O10,[[0,1],[2,0]])
assert rank(O12)==12 and preserves(R12,O12) and preserves(M12,O12)
# Global value reflection (c,v)->(-c,-v) cannot preserve a nonzero
# Heisenberg commutator: omega(-v,-w)=omega(v,w), not -omega(v,w).
assert O12[0][1]==1 and (-O12[0][1])%3==2
# Unlike the uncorrected source reflection (a,c,b)->(-a,-c,-b),
# the map (a,c,b)->(-a,-c+a.b,-b) reverses the multiplication order.
# In the symmetrised central chart t=c+a.b this is simply (t,v)->(-t,-v).
# Verify on all 3^9 states against 9 generators (the algebraic proof
# extends by bilinearity); no source S3 group automorphism is inferred.
def add4(x,y): return tuple((a+b)%3 for a,b in zip(x,y))
def minus4(x): return tuple(-a%3 for a in x)
def dot4(x,y): return sum(a*b for a,b in zip(x,y))%3
def h4_mul(x,y):
    a,c,b=x; aa,cc,bb=y
    return add4(a,aa),(c+cc+dot4(b,aa))%3,add4(b,bb)
def corrected_value_anti(x):
    a,c,b=x
    return minus4(a),(-c+dot4(a,b))%3,minus4(b)
def anti_certificate():
    zero=(0,)*4
    gens=[(zero,1,zero)]
    for i in range(4):
        e=tuple(int(i==j) for j in range(4))
        gens.extend([(e,0,zero),(zero,0,e)])
    checked=0
    for state in itertools.product(range(3),repeat=9):
        x=(state[:4],state[4],state[5:])
        assert corrected_value_anti(corrected_value_anti(x))==x
        for y in gens:
            assert corrected_value_anti(h4_mul(x,y))==h4_mul(
                corrected_value_anti(y),corrected_value_anti(x))
            checked+=1
    assert checked==177147
    return checked


# This T is the literal original Gauge.FourOneFour edge4/corner4 ->
# (tE,tC,bE,bC,XE,YE,XC,YC) map, not an abstract character isomorphism.
# Over F3 its rows are orthogonal with weights 1,1,1,1,2,2,1,1.
def matvec(A,v):
    return tuple(sum(a*b for a,b in zip(row,v))%3 for row in A)

def source_chart_certificate():
    weights=(1,1,1,1,2,2,1,1)
    D=[[int(i==j)*weights[i] for j in range(8)] for i in range(8)]
    assert product(T,transpose(T))==D
    inverse=product(transpose(T),D)
    assert product(T,inverse)==identity(8)
    assert product(inverse,T)==identity(8)
    states=0
    for raw in itertools.product(range(3),repeat=8):
        char=matvec(T,raw)
        assert matvec(inverse,char)==raw
        for source,repair in ((R,R10),(M,M10)):
            observed=matvec(T,matvec(source,raw))
            embedded=matvec(J,char)
            predicted=matvec(repair,embedded)
            assert observed==tuple(predicted[j] for j in (0,1,2,4,6,7,8,9))
        states+=1
    assert states==6561
    return states*3

def audit():
    source_roundtrips=source_chart_certificate()
    x={f"r={r},m={m}":all_forms(r,m) for r in (1,2) for m in (1,2)}
    assert all(v["max_rank"]==6 for v in x.values())
    return {"schema":"jfine-d4-symplectic-maxcut-v1","field":3,
      "source":"dashi_agda IIT PR #1148 existing D4 operators",
      "shell_character":"2A1+B1+B2+2E",
      "original_GaugeFourOneFour_source_chart_roundtrips":source_roundtrips,
      "source_chart_D4_action_equivariant":True,
      "source_T_inverse_weights":[1,1,1,1,2,2,1,1],
      "multiplier_forms":x,"all_rank_eight_forms_excluded":True,
      "minimal_extra_dimensions":2,"repaired_rank":rank(O10),
      "source_restriction_rank":rank(O8),"h6_sized_rank":rank(O12),
      "d4_acts_symplectically_on_repair":True,
      "value_s3_reflection_cannot_lift_as_group_automorphism":True,
      "quadratically_corrected_value_anti_automorphism_generator_checks":anti_certificate(),
      "actual_monster_intertwiner":False,"agda_kernel_checked":False}
if __name__=="__main__":print(json.dumps(audit(),indent=2,sort_keys=True))
