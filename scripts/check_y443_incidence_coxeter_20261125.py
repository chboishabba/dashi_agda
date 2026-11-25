#!/usr/bin/env python3
"""Exact Coxeter action on the existing Singer Levi wheel and JMD source words.
Not a Monster representation. No CI or kernel acceptance.
"""
from itertools import combinations, product
from functools import reduce
from math import gcd
import sympy as S

def require(ok, label):
    if not ok:
        raise RuntimeError(label)

M=S.Matrix([[1,1,0],[0,1,1],[1,1,1]])
r=S.Matrix([1,1,1]); N=M.inv_mod(3).T
bal=lambda v: tuple((int(x)+1)%3-1 for x in v)
canon=lambda v: min(v,tuple(-x for x in v))
P=[bal(M**i*r) for i in range(13)]
L=[bal(N**i*r) for i in range(13)]
dot=lambda a,b: sum(x*y for x,y in zip(a,b))
D={i for i in range(13) if dot(P[i],L[0])%3==0}
require(D=={0,6,10,11},'source offsets')
B=S.Matrix(13,13,lambda i,j:int(dot(P[i],L[j])%3==0))
I=S.eye(26); Z=S.zeros(13)
K=2*I-Z.row_join(B).col_join(B.T.row_join(Z))
raw=[(0,(1,1,1)),(1,(1,0,-1)),(0,(1,0,1)),(1,(1,-1,-1)),(0,(0,1,-1)),(1,(0,1,-1)),(0,(0,1,1)),(1,(1,-1,1)),(0,(1,0,-1)),(1,(1,-1,0)),(0,(0,0,1)),(1,(1,1,0))]
idx=[{canon(v):i for i,v in enumerate(a)} for a in (P,L)]
image=[13*b+idx[b][canon(v)] for b,v in raw]
E={(0,1),(1,2),(2,3),(3,4),(0,5),(5,6),(6,7),(7,8),(0,9),(9,10),(10,11)}
A=2*S.eye(12)
for i,j in E:A[i,j]=A[j,i]=-1
require(K.extract(image,image)==A,'induced source Gram')
R=[I-I[:,i]*K[i,:] for i in image]
Q=[S.eye(12)-S.eye(12)[:,i]*A[i,:] for i in range(12)]
for i,g in enumerate(R):
    require(g*g==I and g!=I and g.T*K*g==K,'involution and form')
    require(g.extract(image,image)==Q[i] and all(g[j,i0]==0 for j in range(26) if j not in image for i0 in image),'invariant source span')
for i,j in combinations(range(12),2):
    m=3 if (i,j) in E else 2
    require((R[i]*R[j])**m==I and R[i]*R[j]!=I,'exact pair order')

def word(w,actors=R):
    out=S.eye(actors[0].rows)
    for i in w:out=out*actors[i]
    return out

uword=[11,10,9,0,1,2,3,4]; betaword=[5,6,7,8]
spider=[0,1,2,0,5,6,0,9,10]; central=[0,9,10,11,1,2,5]
u=word(uword); beta=word(betaword); v=u*R[4]*beta; w=u.inv()*v
require(u**9==I and beta**5==I and w==R[4]*beta,'source path words')
require(w**5==R[4] and w**6==beta,'JMD fifth sixth')
recovered={}
for k in range(9):
    g=u**k*R[4]*u**(-k)
    for j,t in enumerate(R):
        if g==t:recovered[j]=('u',k)
require(set(recovered)==set(uword),'first source path recovery')
gamma=R[0]*beta
require(gamma**6==I,'third path order')
for k in range(6):
    g=gamma**k*R[0]*gamma**(-k)
    for j,t in enumerate(R):
        if g==t:recovered[j]=('gamma',k)
require(len(recovered)==12,'all twelve in generated image')
# Actual permutation conjugation under the 26 source wheel/polarity charts.
for b,k in product(range(2),range(13)):
    perm=[13*((t//13)^b)+(((-1)**b*(t%13)+k)%13) for t in range(26)]
    require(K.extract(perm,perm)==K,'wheel polarity Gram covariance')
    for i,t in enumerate(image):
        g=I-I[:,perm[t]]*K[perm[t],:]
        require(g.extract(perm,perm)==R[i],'transport actual operator')
# Relator obstruction on selected invariant 12-dimensional subspace.
I12=S.eye(12); H=word(spider,Q); C=word(central,Q); U=H**10-I12
require(A.det()==-35,'selected form determinant')
require([U.rank(),(U**2).rank(),(U**3).rank()]==[2,1,0],'spider nilpotent residual')
require((C**9-I12).rank()==7 and C**18==I12,'central residual involution')
require(reduce(gcd,map(int,U))==1 and reduce(gcd,map(int,C**9-I12))==1,'no scalar characteristic repair')
# Saturation: integer combinations of A*U entries generate 1 (Bezout).
# Applying (I-s_i) to each residual column yields that entry times e_i.
# Connected unit off-diagonal edges move it to any root by (I-s_j).
# Thus any invariant submodule containing im(U) contains every root over Z.
require(reduce(gcd,map(int,A*U))==1,'integral residual generates root lattice')
seen={0}
while True:
    more=seen|{j for i in seen for j in range(12) if A[i,j]==-1}
    if more==seen:break
    seen=more
require(len(seen)==12,'unit edge propagation')
# Literal integer certificate for the Bezout step (two entries suffice).
vals=set(map(int,A*U)); cert=next((a,b) for a,b in product(sorted(vals),repeat=2) if gcd(a,b)==1)
print('PASS 78 Coxeter relations on 26-dimensional incidence lattice; selected Gram det -35')
print('PASS JMD source u/v words recover all 12 image generators',sorted(recovered.items()))
print('PASS 312 operator conjugations across 26 wheel/polarity frames')
print('PASS spider residual ranks 2,1,0; central involution residual rank 7')
print('PASS invariant quotient killing spider kills entire selected root lattice; Bezout entries',cert)
