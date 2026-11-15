#!/usr/bin/env python3
"""Independently check universal three-by-three Q(zeta3) identities.

Formal polynomial identities in commuting coefficient variables, not sampled
numeric matrices, and NOT an Agda kernel proof. The existing SU(N) matrix
carrier is the canonical owner. Uses ζ²+ζ+1=0 throughout.
"""
import sympy as s
from time import perf_counter

N=3
symbol=lambda letter:[[tuple(s.Symbol(f'{letter}{i}{j}{k}') for k in range(2)) for j in range(N)]for i in range(N)]
A,B,C=symbol('a'),symbol('b'),symbol('c')
z=lambda:(s.S.Zero,s.S.Zero)
o=lambda:(s.S.One,s.S.Zero)
add=lambda p,q:(p[0]+q[0],p[1]+q[1])
neg=lambda p:(-p[0],-p[1])
star=lambda p:(p[0]-p[1],-p[1])
# ζ²=-1-ζ. Unreduced symbolic polynomials retain syntactic distributivity;
# expand only upon comparing lhs vs rhs.
def mul(p,q):
 a,b=p;c,d=q
 return (a*c-b*d,a*d+b*c-b*d)
def sumq(iterable):
 q=z()
 for t in iterable:q=add(q,t)
 return q
def mm(X,Y):return [[sumq(mul(X[i][k],Y[k][j]) for k in range(N))for j in range(N)]for i in range(N)]
def adj(X):return [[star(X[j][i])for j in range(N)]for i in range(N)]
def det(X):
 a,b,c=X[0];d,e,f=X[1];g,h,i=X[2]
 return add(sumq([mul(a,mul(e,i)),mul(b,mul(f,g)),mul(c,mul(d,h))]),neg(sumq([mul(c,mul(e,g)),mul(b,mul(d,i)),mul(a,mul(f,h))])))
def eq(p,q):return all(s.expand(a-b)==0 for a,b in zip(p,q))
def meq(X,Y):return all(eq(X[i][j],Y[i][j]) for i in range(N) for j in range(N))

t0=perf_counter()
checks={
 'qzeta_conjugation_involutive':eq(star(star(A[1][2])),A[1][2]),
 'qzeta_conjugation_multiplicative':eq(star(mul(A[1][2],B[2][0])),mul(star(A[1][2]),star(B[2][0]))),
 'matrix_identity_left': meq(mm([[o() if i==j else z() for j in range(N)]for i in range(N)], A),A),
 'matrix_identity_right':meq(mm(A,[[o() if i==j else z() for j in range(N)]for i in range(N)]),A),
 'matrix_associativity':meq(mm(mm(A,B),C),mm(A,mm(B,C))),
 'matrix_dagger_involutive':meq(adj(adj(A)),A),
 'matrix_dagger_antihom':meq(adj(mm(A,B)),mm(adj(B),adj(A))),
 'matrix_determinant_multiplicative':eq(det(mm(A,B)),mul(det(A),det(B))),
 'matrix_determinant_dagger':eq(det(adj(A)),star(det(A))),
 'matrix_identity_determinant_one':eq(det([[o() if i==j else z() for j in range(N)]for i in range(N)]),o()),
}
print('elapsed',perf_counter()-t0)
for k,v in checks.items():print(k,'PASS'if v else'FAIL')
assert all(checks.values()),checks
