#!/usr/bin/env python3
"""Original YM D1: exact signed two-mark and physical-geometry adversarial tests.

Attribution: source targets are existing DASHI R494/R496, R429/P06 and original
Wilson physical-shell modules. Kotecky--Preiss (1986) is an imported theorem.
This is a finite rational model / compiler regression, NOT the original Wilson
physical activity estimate, continuum YM or Agda/Lean kernel certificate.
"""
from sympy import symbols, exp, log, diff, simplify, Rational, Matrix

u,v,s,t=symbols("u v s t",real=True)
Z=1+u*exp(s)+v*exp(t)
cov=simplify(diff(log(Z),s,t).subs({s:0,t:0}))
assert cov == -u*v/(1+u+v)**2
z=Rational(1,16)
assert simplify(cov.subs({u:z,v:z})) == -Rational(1,324)
# With each polymer incompatible with itself and the other, KP sum is 2*z*e=e/8<1.
# With diameter=0 for both supports and arbitrary nonlocal incompatibility, KP
# does not constrain physical placement of the incompatible pair.
# For m=1 and dist=10 the proposed 1-root bound is z*e*e^-10=e^-9/16,
# < 3/(16*2^10) < 1/324, using 2<e<3.
assert Rational(3,16*2**10) < Rational(1,324)
# Exact connected-mark cancellation
Z0=1+u+v
assert simplify(0-(u/Z0)*(v/Z0)-cov)==0

# Physical weighted-path alternative. The theorem states that for nonnegative
# K and physical metric d with triangle inequality, and b>1, if
# max_x sum_y K[x,y]*b**d(x,y)<=q<1, then the summed path connection
# P=K+K^2+... has P[x,y]<=q/(1-q)*b**(-d(x,y)).
N=6
K=Matrix(N,N,lambda i,j: Rational(1,16) if abs(i-j)==1 else 0)
b=2
q=Rational(1,4)
for i in range(N):
    assert sum(K[i,j]*b**abs(i-j) for j in range(N))<=q
P=(Matrix.eye(N)-K).inv()-Matrix.eye(N)
for i in range(N):
    for j in range(N):
        assert 0<=P[i,j]<=q/(1-q)*Rational(1,b**abs(i-j))
assert P[0,N-1]==Rational(16,16451071)
print("PASS exact two-mark source Hessian:",cov,"and cov(1/16,1/16)=-1/324")
print("PASS KP alone does not imply physical clustering without source geometry")
print("PASS local six-site rational resolvent and b=2, q=1/4 weighted tail")
print("distance-5 sum:",P[0,5],"<=",Rational(1,96))
print("PHYSICAL OPEN: Wilson marked-source equality; admissible rooted geometry;")
print("  cutoff/volume-uniform original Wilson activity + large-field tail; E1/D2.")
