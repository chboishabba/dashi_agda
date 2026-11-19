#!/usr/bin/env python3
"""Exact FIRST-TITS cubic Higgs benchmark, not CY Yukawa coefficients.
Classical E6 cubic, supersymmetric F/D terms and matrix rank.
Original Johl Brown/DASHI: Ternary27RationalFirstTitsCarrierExact,
#1106, #1241, selected E32/E33; original Tian-Yau Wilson count owner.
New: explicit Hessian and conditional rank obstruction. The physical
labels A,C,B correspond to the original ordered trace blocks X,Y,Z.
"""
import sympy as s
v=s.symbols('v0:27')
A,B,C=[s.Matrix(3,3,v[k:k+9]) for k in (0,9,18)]
N=A.det()+B.det()+C.det()-s.trace(A*C*B)
E=lambda i,j:s.eye(3)[:,i]*s.eye(3)[j,:]
def at(c):return dict(zip(v,[0]*18+list(c)))
for c in [E(2,1),E(2,2),E(2,1)+E(2,2)]:
    assert all(s.diff(N,q).subs(at(c))==0 for q in v)
    H=s.hessian(N,v).subs(at(c))
    assert (H[:18,:18].rank(),H[18:,18:].rank(),H.rank())==(6,4,10)
# Two independent C multiplets with same left row: all polarized
# determinant gradients vanish (every pair of VEV rows is dependent).
a,b=s.symbols('a b')
c=a*E(2,1)+b*E(2,2)
assert all(z==0 for z in c.adjugate())
# Construct a full-rank permitted ABC family coefficient slice.
# This is a witness of algebraic possibility, NOT a computed CY overlap.
Y=s.eye(7)
M=Y.row_join(Y)
assert M.rank()==7 and M.cols-M.rank()==7
# Conjugate family block 4x4, possible rank 4 pairing at zero VEV.
Mbar=s.eye(4)
assert Mbar.rank()==4
# Pure bilinear pairing with two independent C and conjugate VEVs:
# F=0 requires M vbar=0 and M.T v=0, so rank <= 6-2.
# Explicit maximal-rank witness under this condition.
M=s.zeros(9,6)
for i in range(4):M[i,i]=1
assert M.rank()==4
for i in (4,5):
    assert M*s.eye(6)[:,i]==s.zeros(9,1)
    assert M.T*s.eye(9)[:,i]==s.zeros(6,1)
assert (9-M.rank(),6-M.rank())==(5,2)
print('PASS original cubic Hessian ranks 6+4=10 for each selected rank-one C VEV')
print('PASS common-row two-VEV determinant gradients vanish')
print('PASS admissible ABC family coefficient benchmark rank 7')
print('PASS pure bilinear F-flat bound rank <=4 with two independent conjugate VEVs')
print('OPEN actual CY overlap maps, full Higgs quotient, exotic masses and physical normalization')
