#!/usr/bin/env python3
"""Two-level SU3 Heisenberg clock/shift obstruction for Hatcher tower.

Original roots: Hatcher Algebraic Topology Example 2B.2 gives stage
child-commutator inclusions; classical Heisenberg finite p-group,
Weyl clock-and-shift matrices, derived-series and free-group residual
nilpotence theorems. Existing original C3 geometry/abelian character
result belongs to horn PR #1244; SU3 selected W belongs to #1247.
This is a NEW derived source-test, not a wild geometry/kernel proof.
"""
from itertools import product
from sympy import Matrix, eye, diag, Rational, I, sqrt, simplify, zeros

z = -Rational(1,2)+I*sqrt(3)/2
X = Matrix([[0,0,1],[1,0,0],[0,1,0]])
Z = diag(1,z,z**2)
E = eye(3)
exact=lambda M:M.applyfunc(simplify)
comm=lambda A,B:exact(A*B*A.inv()*B.inv())
assert X.det()==1 and simplify(Z.det())==1
assert exact(X*X.conjugate().T)==E
assert exact(Z*Z.conjugate().T)==E
C=comm(X,Z)
assert C!=E and exact(C-z**2*E)==zeros(3)
assert comm(C,X)==comm(C,Z)==E
assert comm(C,comm(Z,X))==E
print("PASS exact SU3 first clock/shift commutator central !=I, second level I")

# Normal forms X^a Z^b zeta^c, a,b,c mod3. The 27
# elements form a two-step nilpotent group, commutators central.
mul=lambda x,y:((x[0]+y[0])%3,(x[1]+y[1])%3,
                 (x[2]+y[2]+x[1]*y[0])%3)
inv=lambda x:((-x[0])%3,(-x[1])%3,(-x[2]+x[0]*x[1])%3)
comm3=lambda x,y:mul(mul(mul(x,y),inv(x)),inv(y))
G=list(product(range(3),repeat=3))
unit=(0,0,0)
for g in G:
    assert mul(g,inv(g))==unit
    for h in G:
        assert comm3(g,h)[:2]==(0,0)
        assert comm3(comm3(g,h),(1,0,0))==unit
        assert comm3(comm3(g,h),(0,1,0))==unit
assert comm3((1,0,0),(0,1,0))==(0,0,2)
print("PASS all 729 Heisenberg pairs: commutator central, depth2 trivial")
print("STOP: nontrivial first-depth finite SU3 test != compatible all-depth Hatcher representation")
print("OPEN actual wild source maps, meridian Euclidean lengths and kernel proof")
