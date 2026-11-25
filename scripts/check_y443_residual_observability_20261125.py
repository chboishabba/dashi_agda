#!/usr/bin/env python3
"""Selected Y443 Coxeter observer: retained future-response fibres, not Monster."""
from itertools import product
import sympy as s
from sympy.matrices.normalforms import smith_normal_form
from sympy.polys.domains import ZZ

def require(ok, label):
    if not ok: raise RuntimeError(label)

I=s.eye(12); A=2*I
edges=((0,1),(1,2),(2,3),(3,4),(0,5),(5,6),(6,7),(7,8),(0,9),(9,10),(10,11))
for i,j in edges: A[i,j]=A[j,i]=-1
Q=[I-I[:,i]*A[i,:] for i in range(12)]
def word(w):
    out=I
    for i in w: out=out*Q[i]
    return out
H=word((0,1,2,0,5,6,0,9,10))**10
C=word((0,9,10,11,1,2,5))**9
U=H-I; V=C-I
require(A.det()==-35 and U**3==s.zeros(12) and C*C==I,'source checks')
# Row lattice basis via column HNF, with original rows preserved in witness list.
from sympy.matrices.normalforms import hermite_normal_form

def hnf_rows(M): return hermite_normal_form(M.T).T

def observe(D, depth):
    W=hnf_rows(D); ranks=[W.rows]; smith=[]
    for k in range(depth+1):
        sn=smith_normal_form(W,domain=ZZ)
        smith.append(tuple(abs(int(sn[i,i])) for i in range(W.rows)))
        if k<depth:
            W=hnf_rows(s.Matrix.vstack(W,*[W*q for q in Q])); ranks.append(W.rows)
    return W,ranks,smith
for label,D,expected in [('spider',U,[2,10,12,12]),('central',V,[7,9,11,12]),('joint',U.col_join(V),None)]:
    W,ranks,smith=observe(D,3)
    if expected: require(ranks==expected,label+' ranks')
    print(label,ranks,smith)
    require(W.rows==12,label+' full rational recovery')
    # all future responses on Z^12 determine v; rational decoding is exact.
    require(W.inv()*W==I,label+' decoder')
    # Each full lattice row lies in root form row lattice, as each D is a
    # sum of right products of generator defects, and A Q=Q^-T A.
    require(all(x.q==1 for x in W*A.inv()),label+' root-form containment')
# Canonical integer-form observer and its residue obstruction.
for p in (2,3,5,7,11,13):
    # modular Gaussian elimination, never use characteristic-zero rank here.
    def rank_mod(B):
        B=[[int(x)%p for x in row] for row in B.tolist()]; k=0
        for j in range(len(B[0])):
            pivot=next((i for i in range(k,len(B)) if B[i][j]),None)
            if pivot is None: continue
            B[k],B[pivot]=B[pivot],B[k]; z=pow(B[k][j],-1,p); B[k]=[x*z%p for x in B[k]]
            for i in range(k+1,len(B)):
                z=B[i][j]; B[i]=[(a-z*b)%p for a,b in zip(B[i],B[k])]
            k+=1
            if k==len(B):break
        return k
    rows=[observe(D,3)[0] for D in (U,V,U.col_join(V))]
    print('mod',p,rank_mod(A),*[rank_mod(W) for W in rows])
# Integer stabilization is stronger than rational rank saturation.
for name,D,depth,indices in [('spider',U,4,[315,105,35]),('central',V,7,[2240,560,140,70,35]),('joint',U.col_join(V),2,[35])]:
    W,ranks,smith=observe(D,depth)
    require(hnf_rows(A)==W,name+' exact root-form row lattice')
    require(hnf_rows(s.Matrix.vstack(W,*[W*q for q in Q]))==W,name+' integral stabilization')
    from math import prod
    full=[prod(t) for t in smith if len(t)==12]
    print(name,'full-rank indices',full,'stabilizes by',depth)
    require(full==indices,name+' exact index history')
# Concrete signed consumer collisions, using literal node labels e1/d1/a.
v=I[:,4]; zero=s.zeros(12,1)
require(U*v==V*v==zero,'joint zero at depth zero')
require((U*Q[3]*v)[0]==48 and (U*Q[3]*(-v))[0]==-48,'signed future witness')
# For every ring, fixed Gram radical is hidden from all reflection words.
require(all(q-I==-I[:,i]*A[i,:] for i,q in enumerate(Q)),'radical factorization')
print('PASS exact integral stabilizations and signed 0/+48/-48 consumer collision')
