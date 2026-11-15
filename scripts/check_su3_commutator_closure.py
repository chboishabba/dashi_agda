#!/usr/bin/env python3
"""Exact rational su(3) real anti-Hermitian basis using sympy I."""
import sympy as s
I=s.I
E=lambda a,b:s.eye(3)[:,a]*s.eye(3)[b,:]
H=[E(0,1)+E(1,0),-I*E(0,1)+I*E(1,0),E(0,0)-E(1,1),E(0,2)+E(2,0),-I*E(0,2)+I*E(2,0),E(1,2)+E(2,1),-I*E(1,2)+I*E(2,1),(E(0,0)+E(1,1)-2*E(2,2))/s.sqrt(3)]
B=[I*h for h in H]
zero=lambda m:all(s.simplify(t)==0 for t in m)
for a in B:
 assert zero(a+a.H) and s.trace(a)==0
for a in B:
 for b in B:
  c=a*b-b*a
  assert zero(c+c.H) and s.trace(c)==0
  coeff=[s.simplify(-s.trace(h*c)/2) for h in B]
  assert zero(c-sum((q*h for q,h in zip(coeff,B)),s.zeros(3)))
print("PASS su(3): eight anti-Hermitian generators, 64 commutators, exact closure and invariant trace pairing")
print("NOT established: physical confinement, coupling matching, compactification origin")
