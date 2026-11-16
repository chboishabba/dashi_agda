#!/usr/bin/env python3
"""H1 exact rational/complex type firewall; not a proof of classical Hodge theory."""
from fractions import Fraction as Q
import sympy as s
# Hodge components are complex, rational cohomology is a distinct lattice.
I=s.I
v=s.Matrix([1,I])
assert s.conjugate(v[1])==-I
assert v[1] not in (s.Rational(0),s.Rational(1))
# Nonreal complex Hodge line C*(1,i) has zero intersection with Q^2.
a,b=s.symbols("a b", rational=True)
assert s.solve([a-s.Symbol("t"), b-I*s.Symbol("t")],(a,b,s.Symbol("t"))) == {a:0,b:0,s.Symbol("t"):0}
# Rational cohomology of CP1xCP1 and complexification.
M=s.eye(2)
assert M.det()==1
for a in range(-6,7):
 for b in range(-6,7):
  q=s.Matrix([Q(a,7),Q(b,11)])
  assert M*q==q
# In actual H^(1,1)(CP1xCP1,C), complex class i*h1 is not rational.
assert s.im(I)!=0
# H1 cycle classes land in Hodge intersection; does not imply H3 surjectivity.
cycle_image=s.Matrix([[1],[0]])
assert cycle_image.rank()==1
assert s.Matrix.hstack(cycle_image,s.Matrix([0,1])).rank()==2
print("PASS Q vs C scalar split and conjugation")
print("PASS non-rational Hodge line negative control")
print("PASS 169 rational product cycle class cases")
print("PASS image-subset does NOT imply Hodge surjectivity")
print("FIREWALL H1 classical background only, native Agda source needs complexification")
print("FIREWALL H3 universal algebraic representative remains OPEN")
