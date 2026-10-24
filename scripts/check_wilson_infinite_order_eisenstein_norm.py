#!/usr/bin/env python3
"""Exact infinite-order obstruction for the selected SU3 Wilson W.

ORIGINAL SOURCE: sibling Agda #1247 selected W trace in Q(zeta3),
where zeta3^2+zeta3+1=0. General prior mathematics: eigenvalues of
finite-order matrices are roots of unity, algebraic integers are closed
under sums, and field traces/norms of algebraic integers are integers.
Eisenstein algebraic integers in Q(zeta3) have ring Z[zeta3].
NEW cross-PR inference: W has INFINITE ORDER, hence cannot be the image
of any element under ANY finite-image representation, not only A5.
No inference about geometric horn holonomy, physical field selection,
or unitarity beyond the separately selected W source is made here.
"""
from fractions import Fraction as Q
from math import gcd
A=176093404722400
B=-19836986431118
D=181846007130841
assert D>0
assert gcd(gcd(abs(A),abs(B)),D)==1
alpha=Q(A,D)
beta=Q(B,D)
assert beta!=0
# For zeta3^2+zeta3+1=0, its conjugate is zeta3^2=-1-zeta3.
# The algebraic trace/norm of t = alpha+beta*zeta3 to Q are:
Tr=2*alpha-beta
Nm=alpha*alpha-alpha*beta+beta*beta
assert Tr==Q(442358853598,216225930001)
assert Nm==Q(34895555697482945411132133124,33067970309429875820893367281)
assert 2<Tr<3 and 1<Nm<2
assert Tr.denominator!=1 and Nm.denominator!=1
print('PASS exact Eisenstein field trace:',Tr,'strictly 2 < Tr < 3')
print('PASS exact Eisenstein field norm:',Nm,'strictly 1 < Nm < 2')
# If W^n = I, eigenvalues are roots of x^n-1 hence algebraic integers.
# t = Tr_matrix(W) is an algebraic integer; its K/Q field trace and
# norm must be RATIONAL INTEGERS. Both calculated invariants violate it.
print('NO-GO: W has finite order (algebraic integer field-trace contradiction)')
print('NO-GO: W belongs to the image of ANY FINITE GROUP representation')
# Absolute elementary check from ring-of-integers Z[zeta3]:
assert alpha.denominator!=1 and beta.denominator!=1
print('PASS independent Z[zeta3] integrality witness: both basis coefficients nonintegral')
# Hatcher's perfect group can map to nonabelian infinite images;
# finite-image no-go for this W does NOT block its use as an
# abstract root under some other compatible SU3 group representation.
print('BOUNDARY: infinite order does not prove existence of a compatible Hatcher tower')
print('BOUNDARY: no local smooth/bounded SU3 connection or physical neutrino realization certified')
