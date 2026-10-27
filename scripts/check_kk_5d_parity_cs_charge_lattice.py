#!/usr/bin/env python3
"""NECESSARY 5D SU3 x U1 parity/CS charge-lattice arithmetic, not sufficient anomaly proof.
Six quarks plus two additional vectorlike colour-triplet Dirac fields.
U1 integer lattice charges are three times physical electron-normalized Q.
See Bonetti, Grimm, Hohenegger JHEP07(2013)043, and 5d anomaly literature.
"""
from fractions import Fraction
charges=(2,-1,-1,2,-1,2,2,-1)
assert len(charges)==8 and all((1+q)%3==0 for q in charges)
assert (-3)%3==0 # ordinary colourless electron integer-charge convention
power_sums=[sum(q**n for q in charges) for n in range(4)]
assert power_sums == [8,4,20,28]
half_shifts=[Fraction(x,2) for x in power_sums]
assert half_shifts == [4,2,10,14]
for i in range(8):
    signs=[1]*8;signs[i]=-1
    assert all(Fraction(sum(signs[j]*charges[j]**n for j in range(8)),2).denominator==1 for n in range(4))
# Candidate adjoint Dirac fermion additionally has doubled Dynkin index 6,
# so a conventionally normalised SU3 parity half-shift of 3 is integral.
assert (6//2)==3
print("PASS elementary q3/triality congruence; power sums n=0..3",power_sums)
print("PASS necessary conventional half-shift integrality",half_shifts,"adjoint",3)
print("LIMIT quotient (SU3xU1)/Z3 spin-CS lattice, gravitational/mixed terms, APS eta, light modes, bare integer levels and regulator still OPEN")

# A charged SU3 fundamental contains THREE colour components in a PURE U1 trace.
# Pure U1-gravity and U1^3 formal parity moments therefore need dim(R)=3:
assert sum(charges)*3==12 and sum(q**3 for q in charges)*3==84
assert sum(charges)*3//2==6 and sum(q**3 for q in charges)*3//2==42
print("PASS colour-weighted U1-gravity and U1-cubic formal half moments",6,42)
print("DO NOT identify unweighted [4,2,10,14] with four physical CS levels without trace normalization")
