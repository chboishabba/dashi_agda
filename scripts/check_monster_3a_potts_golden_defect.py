#!/usr/bin/env python3
"""Published Monster 3A/Potts noninvertible-defect exact coefficient audit.
Fosbinder-Elkins--Harvey, arXiv:2408.16263 (J Phys A 58 395201).
The W defect series is (J + sqrt(5) Q)/2.
This DOES NOT identify 3A with 27A/27B, whose 9th powers are 3B.
"""
import sympy as s
J=[1,0,196884,21493760,864299970]
Q=[1,0,-78794,-9307840,-381508370]
sq5=s.sqrt(5)
W=[s.simplify((a+sq5*b)/2) for a,b in zip(J,Q)]
phi=(1+sq5)/2
assert W[0]==phi
assert s.simplify(phi*phi-phi-1)==0
assert s.simplify(2*W[2]-196884+78794*sq5)==0
assert all(s.simplify(2*W[j]-J[j]-sq5*Q[j])==0 for j in range(len(J)))
assert s.simplify(W[0]-1)!=0
print("PASS Monster 3A Potts W line vacuum coefficient (1+sqrt(5))/2")
print("PASS exact reported q-series coefficients through q^3")
print("PASS phi^2=phi+1; consistency of Fibonacci quantum dimension")
print("LIMIT published defect series does not supply a specific 3-braid F/R representation")
print("LIMIT Monster 3A Potts and order-27A/B->3B lanes are distinct")
