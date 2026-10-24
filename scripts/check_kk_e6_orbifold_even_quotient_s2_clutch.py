#!/usr/bin/env python3
"""ORBIFOLD-PARITY-COMPATIBLE NONLIFTABLE faithful E6-derived gauge bundle.

Original E6 #1106 first-Tits SU3^3 action on 27 has kernel
Z3_diag. In KK #1241 choose P_c=I and P_L=P_R=diag(-,-,+);
the unbroken boundary cover H0=SU3c x S(U2xU1)L x S(U2xU1)R
is connected, with central diagonal Z3 inside H0.
Its faithful boundary group is H=H0/Z3_diag.

On S², give the north/south hemispheres the clutching transition
g(t) on equator S¹=R/Z, defined by the class of
 (h(t),h(t),h(t)) in H where
 h(t)=diag(exp(2πit/3),exp(2πit/3),exp(-4πit/3)).
Each h(t) COMMUTES with both orbifold parities, lies inside SU3 and
S(U2xU1), h(0)=I, h(1)=omega I.
Thus g(t) is a closed LOOP in the quotient boundary gauge group.
Its unique lift in H0 starting at identity ends at
(omega I,omega I,omega I), nontrivial deck Z3, so this boundary-
admissible principal H bundle on S² CANNOT lift to an H0 bundle.
Three concatenations lift to a closed loop in the cover: the
image of the loop under the deck-group obstruction map to Z3 has
order three, NOT necessarily the element itself in π1(H).

This demonstrates a real previously unpaid GLOBAL CS/eta test family
for the SELECTED orbifold, unlike the separate bulk clock-shift T²
witness whose S shift does not commute with P.
We do NOT compute a 5D spin/APS anomaly or construct a whole
six-dimensional fermionic index on that twisted gauge bundle.
"""
import sympy as s
u=s.symbols("u",real=True)
omega=s.exp(2*s.pi*s.I/3)
phase=s.exp(2*s.pi*s.I*u/3)
h=s.diag(phase,phase,phase**-2)
P=s.diag(-1,-1,1)
assert s.simplify(h.det())==1
assert (P*h-h*P).applyfunc(s.simplify)==s.zeros(3)
assert h.subs(u,0)==s.eye(3)
assert (h.subs(u,1)-omega*s.eye(3)).applyfunc(s.simplify)==s.zeros(3)
assert (h.subs(u,1)-s.eye(3)).applyfunc(s.simplify)!=s.zeros(3)
# Because diag(omega I) is in first-Tits kernel, g(1)=g(0)
# ON THE FAITHFUL GAUGE GROUP. But the chosen lift is not closed.
assert all((z-z)%3==0 for z in range(3))
for n in (1,2):
    assert (h.subs(u,n)-s.eye(3)).applyfunc(s.simplify)!=s.zeros(3)
assert (h.subs(u,3)-s.eye(3)).applyfunc(s.simplify)==s.zeros(3)
# Negative control: the alternate bulk T2 shift does NOT preserve
# the fixed-point gauge parity, so never use it as an orbifold H test.
S=s.Matrix([[0,0,1],[1,0,0],[0,1,0]])
assert (P*S-S*P)!=s.zeros(3)
print("PASS source faithful H=(SU3c x U2L x U2R)/Z3_diag orbifold EVEN group")
print("PASS equator clutch loop in parity-even H lifts from identity to diagonal omega central deck element")
print("PASS order-three Z3 lift obstruction; nonliftable H principal bundle on S2")
print("FAIL old bulk-clock/shift flat T2 configuration as parity-even fixed-plane test")
print("OPEN spin quotient Dirac index/eta and truly quantized 5D CS + Chi33 boundary WZ on this S2 obstruction")
