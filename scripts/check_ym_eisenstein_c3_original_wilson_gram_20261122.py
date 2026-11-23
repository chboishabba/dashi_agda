#!/usr/bin/env python3
"""Original L=1 Wilson SU(2) commutator/C3 weighted-gram diagnostic.

Uses the original D1=2 sum |Im(q_a) cross Im(q_b)|² identity from
Docs/physics/YMClayOriginalWilsonGaugeCubicMaxCut20261117.md.
Q8 is a FINITE subgroup/reference, not physical Haar SU(2).
All four native link variables are retained, no independent test weight.
Tests finite Gibbs expectation symmetry and C3 Gram sectors, not OS2/OS4,
continuum spectral faithfulness, or Yang-Mills mass gap.
"""
from fractions import Fraction as Q
from itertools import product
from sympy import Matrix, I, sqrt, simplify

checks=0
links=list(product(range(8),repeat=4))
assert len(links)==4096; checks+=1

def axis(q): return q//2

def deficit(q):
    return 2*sum(axis(q[i])!=0 and axis(q[j])!=0 and axis(q[i])!=axis(q[j])
                 for i in range(4) for j in range(i+1,4))

def weight(q): return Q(1,2)**deficit(q)

def rotate(q):return (q[0],q[3],q[1],q[2])

def commutator_trace(q,i,j):
    ai,aj=axis(q[i]),axis(q[j])
    return -1 if ai and aj and ai!=aj else 1

def source_observables(q):
    return tuple(commutator_trace(q,0,j) for j in (1,2,3))

Z=Q(0);means=[Q(0)]*3;gram=[[Q(0)]*3 for _ in range(3)]
for q in links:
    r=rotate(q)
    assert rotate(rotate(r))==q
    assert deficit(q)==deficit(r)
    assert weight(q)==weight(r)
    checks+=3
    f=source_observables(q)
    assert source_observables(r)==(f[2],f[0],f[1])
    checks+=1
    w=weight(q);Z+=w
    for j in range(3):
        means[j]+=w*f[j]
        for k in range(3):gram[j][k]+=w*f[j]*f[k]
assert Z==Q(15451,16);checks+=1
assert all(m/Z==Q(13684,15451) for m in means);checks+=1
assert all(gram[j][j]/Z==1 for j in range(3));checks+=1
assert all(gram[j][k]/Z==Q(12541,15451) for j in range(3) for k in range(3) if j!=k);checks+=1
M=Matrix([[x/Z for x in row] for row in gram])
omega=(-1+sqrt(3)*I)/2
v0=Matrix([1,1,1]);v1=Matrix([1,omega,omega**2]);v2=Matrix([1,omega**2,omega])
assert M*v0==Q(40533,15451)*v0;checks+=1
assert all(simplify(z)==0 for z in M*v1-Q(2910,15451)*v1);checks+=1
assert all(simplify(z)==0 for z in M*v2-Q(2910,15451)*v2);checks+=1
assert Q(2910,15451)>0;checks+=1
mu=means[0]/Z
cov0=Q(40533,15451)-3*mu**2
cov12=Q(2910,15451)
assert cov0==Q(64519815,238733401) and cov12>0;checks+=1
# Distinct source states can have identical observed scalar; do not equate
# vanishing invariant projection with a physical zero-energy state.
assert simplify(1+omega+omega**2)==0 and v1!=Matrix([0,0,0]);checks+=1
# A selected C3-invariant observable cannot see all nontrivial sectors.
assert simplify(v0.conjugate().T*v1)[0]==0;checks+=1
# This strictly positive finite observable Gram is not a reflection-positive
# time-dependent OS Gram, nor does it provide a uniform continuum mass rate.
assert M.det()!=0;checks+=1
print(f'PASS {checks}/{checks} source-specific exact Q8/Wilson C3 checks')
print('4-link original-L1-Q8 configurations:',len(links))
print('Z=',Z,'E[W_01]=',mu)
print('C3 Gram=',M)
print('character eigenvalues: invariant=',Q(40533,15451),', zeta/zeta2=',Q(2910,15451))
print('centered eigenvalues:',cov0,cov12,cov12)
print('UNPAID: physical SU(N) Haar, reflected positive-time Gram, OS null quotient, E1 limits, D1 physical decay, D2 all-sector gap.')
