#!/usr/bin/env python3
"""Faithful first-Tits 27 trinification global group and a non-liftable bundle.

ORIGINAL E6 author: Slansky 1981, and the original first-Tits
M3^3 cubic-preserving SL3^3 action already exists in repo PR #1106.
The SU3³/Z3 subgroup identification is documented in E6 representation
literature; the current code is a SAME-27-source finite audit.

Matter 27=(3,bar3,1)+(bar3,1,3)+(1,3,bar3) has
centre characters (a-b),(-a+c),(b-c) mod 3.
Kernel is EXACTLY three diagonal assignments a=b=c, so faithful
gauge group on 27 is (SU3c×SU3L×SU3R)/Z3_diag.

Concrete non-liftable quotient-holonomy witness on T2:
clock C=diag(1,omega,omega²), shift S cyclic in SU3,
CS=omega SC. Set holonomies [(C,C,C),(S,S,S)] in SU3³.
Their commutator is (omega I,omega I,omega I): NONTRIVIAL
in SU3³ but trivial in diagonal-Z3 quotient, hence a legal commuting
quotient pair with nonzero obstruction to a commuting SU3³ lift.
This is a fixed flat quotient-bundle witness, not a full 5D CS
eta quantization or all H²(-,Z3) classes.

CP3 central U1 flux and S2xS4 instanton index tests in the
earlier script used LIFTABLE product-gauge backgrounds and do
NOT cover the new nonliftable diagonal-Z3 sector.
"""
from itertools import product
import sympy as s
omega=s.exp(2*s.pi*s.I/3)
def mod3(a):return a%3
triples=list(product(range(3),repeat=3))
def chars(a,b,c):return ((a-b)%3,(c-a)%3,(b-c)%3)
kernel=[z for z in triples if chars(*z)==(0,0,0)]
assert kernel==[(0,0,0),(1,1,1),(2,2,2)]
assert len(kernel)==3 and len(triples)==27
assert len(triples)//len(kernel)==9
C=s.diag(1,omega,omega**2)
S=s.Matrix([[0,0,1],[1,0,0],[0,1,0]])
assert s.simplify(C.det())==1 and S.det()==1
assert (C*S-omega*S*C).applyfunc(s.simplify)==s.zeros(3)
comm=(C*S*C.inv()*S.inv()).applyfunc(s.simplify)
assert (comm-omega*s.eye(3)).applyfunc(s.simplify)==s.zeros(3)
assert (comm-s.eye(3)).applyfunc(s.simplify)!=s.zeros(3)
assert chars(1,1,1)==(0,0,0)
for rep_char in chars(1,1,1):assert rep_char==0
print("PASS exact first-Tits 27 central kernel:",kernel)
print("PASS faithful gauge group SU3³ / diagonal Z3, not independent SU3³")
print("PASS quotient T2 clock/shift flat holonomies have NONTRIVIAL diagonal Z3 commutator in cover but commute in quotient")
print("FAIL full global spin-CS promotion from lifted CP3/S2xS4/S2xK3 test-family success")
print("OPEN quotient non-liftable-bundle APS eta and CS global level, actual 5D anomaly-free source")
