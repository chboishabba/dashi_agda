#!/usr/bin/env python3
"""Exact finite audit: spatial cube27/54 versus Monster 3B trace54 and residual53.

Arithmetic and graph owners sourced from DASHI, not measured Monster action
or physical morphic fields. All test cases are exact and synthetic.
"""
from itertools import product, permutations
from sympy import Matrix

n=0
def check(label, expr):
    global n
    assert bool(expr), label
    n+=1
    print(f'PASS {n:02d} {label}')

T=(-1,0,1)
P=tuple(product(T,repeat=3)); index={p:i for i,p in enumerate(P)}
E={tuple(sorted((p,q))) for p in P for q in P if sum(abs(a-b) for a,b in zip(p,q))==1}
# The 54 canonical forward oriented bonds, not a 54-element Monster basis.
Ep=tuple((p,q) for p,q in product(P,repeat=2) if sum(q[i]-p[i] for i in range(3))==1 and sum(abs(q[i]-p[i]) for i in range(3))==1)
check('spatial carrier is exactly T^3, 27 sites',len(P)==27)
check('native cube has 54 unordered positive nearest-neighbour bonds',len(E)==len(Ep)==54)
check('each positive bond orientation unique',all((q,p) not in Ep for p,q in Ep))
check('cube degree strata 8/12/6/1',tuple(sum(sum(p in edge for edge in E)==d for p in P) for d in (3,4,5,6))==(8,12,6,1))

# Exact Monster sources: 3B selected eigenspace multiplicity tuples.
W=(65663,65610,65610); V=(65664,65610,65610)
check('W (196883) selected 3B character multiplicity',sum(W)==196883)
check('weight-two (196884) selected 3B character multiplicity',sum(V)==196884)
check('W has regular C3 bulk 3*65610 and residual 53',3*65610+53==196883)
check('weight-two selected trace is 54, not residual 53',V[0]-V[1]==54 and W[0]-W[1]==53)
check('weight-two regular bulk and trace arithmetic',3*65610+54==196884)
check('candidate six-by-nine 54 vs reduced 45+8',6*9==54 and 5*9+8==53)
check('196884 10*3^9 plus 54 numerical chart',10*3**9+54==196884)
check('54 spatial edge basis and 54 scalar trace cannot be assumed same typed object',len(E)==V[0]-V[1])

# M(x,y,z)=(x+y,x-y,z) over balanced Z/3, acting on cube SITE labels.
def bal(a):return ((a+1)%3)-1
def modular(p):x,y,z=p;return bal(x+y),bal(x-y),z
m={p:modular(p) for p in P}
Em={tuple(sorted((m[p],m[q]))) for p,q in E}
check('selected modular site map is a 27-site permutation',len(set(m.values()))==27)
check('selected modular action fails to preserve native +x bond',tuple(sorted((m[(0,0,0)],m[(1,0,0)]))) not in E)
check('M maps native 54 bonds to distinct 54 nonlocal/mixed bonds',len(Em)==54)
check('M-local common edge support is 18',len(E.intersection(Em))==18)
check('M-local smallest bond closure has 90 edges',len(E.union(Em))==90)
check('symmetric difference has 72 bonds',len(E.symmetric_difference(Em))==72)
check('native cube +x degree 5, M-image degree 4',sum((1,0,0) in e for e in E)==5 and sum(m[(1,0,0)] in e for e in E)==4)
check('cyclic residue carry jumps from +++ to --- instead of an edge',tuple(sorted(((1,1,1),(-1,-1,-1)))) not in E)

L=Matrix.zeros(27,27); U=Matrix.zeros(27,27)
for p,q in E:
    i,j=index[p],index[q]
    L[i,i]+=1;L[j,j]+=1;L[i,j]-=1;L[j,i]-=1
for p in P:U[index[m[p]],index[p]]=1
C=L*U-U*L
check('native cube Laplacian has total weighted degree 108',sum(L[i,i] for i in range(27))==108)
check('selected modular M fails adjacency-Hamiltonian commutation',C!=Matrix.zeros(27,27))
check('actual cube Laplacian commutator squared norm is 168',sum(v*v for v in C)==168)
check('actual cube Laplacian commutator rank is 24',C.rank()==24)

# All explicitly signed coordinate permutations are cube graph automorphisms.
A=[]
for perm in permutations(range(3)):
    for signs in product((-1,1),repeat=3):
        transform=lambda p:tuple(signs[i]*p[perm[i]] for i in range(3))
        A.append(tuple(transform(p) for p in P))
check('48 signed coordinate/axis permutation actions are distinct',len(set(A))==48)
check('all 48 signed axis permutations preserve all 54 native bonds',all({tuple(sorted((a[index[p]],a[index[q]]))) for p,q in E}==E for a in A))
check('27 does not divide 48, so these 48 actions have no element order27',48%27 != 0)
print(f'{n}/{n} exact Monster-vs-native-geometry checks PASS')
