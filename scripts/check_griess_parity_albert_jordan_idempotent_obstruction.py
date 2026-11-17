#!/usr/bin/env python3
"""Actual native rational Albert: selected antipodal parity C13 and Jordan NO-GO.

Original source Griess Jr., J Algebra 131 (1990) 281-293;
native rational Jordan coordinates: Lean #52, original signed P3^3
antipode and 13-axis source: Agda #1249 / #1261.
This is a subsequent exact computation; NO Lean/Agda kernel receipt.

Usage: python checker.py cyclic_basis_certificate.json traceless26_certificate.json
"""
import json,sys
from pathlib import Path
import sympy as s
if len(sys.argv)!=3:raise SystemExit('usage: checker.py cyclic_basis.json native_traceless26.json')
d=json.loads(Path(sys.argv[1]).read_text())
b=json.loads(Path(sys.argv[2]).read_text())
X=s.Matrix([[s.Rational(y) for y in row]
    for row in d['native_traceless_albert_to_two_grade_cycle_intertwiner']])
B=s.Matrix([[s.Rational(y) for y in row]
    for row in b['native_albert26_traceless_order13_matrix']])
I=s.eye(13)
T=s.BlockMatrix([[I,I],[I,-I]]).as_explicit()
Y=X*T
P=s.zeros(13)
for k in range(13):P[(k+1)%13,k]=1
assert X.det()==-s.Rational(729,4096)
assert T.det()==-8192 and Y.det()==1458
assert B*Y==Y*s.diag(P,P)
D=s.diag(I,-I);J=Y*D*Y.inv()
assert J*J==s.eye(26) and J*B==B*J and s.trace(J)==0
# Original ACTUAL native tracezero basis, not 26 site positions.
C=s.zeros(27,26);C[0,0]=1;C[1,0]=-1;C[1,1]=1;C[2,1]=-1
for k in range(24):C[3+k,2+k]=1
G=C.T*s.diag(*([1]*3+[2]*24))*C
assert J.T*G*J==G
Q=s.zeros(26,27);Q[0,0]=1;Q[1,2]=-1
for k in range(24):Q[2+k,3+k]=1
unit=s.Matrix([1,1,1]+[0]*24)
tr=s.Matrix([[1,1,1]+[0]*24])
E=C*J*Q*(s.eye(27)-unit*tr/3)+unit*tr/3
assert E*unit==unit and E**2==s.eye(27) and tr*E==tr
assert E*C[:,0]==C[:,1] and E*C[:,1]==C[:,0]
# Actual primitive diagonal Jordan idempotent e0=(1,0,0).
# The native H3(O_Q) Jordan product is coordinatewise on diagonals.
e0=s.eye(27)[:,0];bad=E*e0
assert tuple(bad[:3])==(s.Rational(2,3),s.Rational(2,3),-s.Rational(1,3))
bad2=s.Matrix([bad[i]*bad[i] if i<3 else 0 for i in range(27)])
assert tuple(bad2[:3])==(s.Rational(4,9),s.Rational(4,9),s.Rational(1,9))
assert bad2!=bad
print('PASS parity-adapted native Albert C13 basis Y: det=1458, BY=Y(P13⊕P13)')
print('PASS selected J²=I26, J commutes with B, J trace-Gram orthogonal')
print('PASS unital extension E swaps selected native A2 traceless diagonal roots')
print('PASS E maps actual Jordan idempotent e0 to NON-idempotent (2/3,2/3,-1/3)')
print('NOT a Jordan automorphism, selected Monster VOA/physical action, or kernel proof')
