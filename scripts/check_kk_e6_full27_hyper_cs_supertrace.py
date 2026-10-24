#!/usr/bin/env python3
"""5D E6/Sl3^3 physical source: full 27 hyper vs 2-bifundamental truncation.

Original repo donor #1106: first-Tits literal 27=(3,bar3,1)
+ (bar3,1,3)+(1,3,bar3), two E32/E33 VEVs, 12 broken LR
vectors, transverse Hessian on 36-REAL subspace.
External original 5D vector/hyper SUSY multiplet content is cited
in #1241 docs. This is exact representation/DOF + conditional parity
arithmetic, NOT an established on-shell 5D SUSY action or E6 vacuum.
"""
from fractions import Fraction as F
# 5D 1 massless gauge: 3 pol; massive 5D vector: 4 pol.
lr_generators=16
lr_broken=12
lr_unbroken=4
assert 16*3+36==4*3+12*4+24==84
# The original local 36-real source is two complex (3,bar3) matrices.
# Two *full* complex 27s contain 108 real coordinates.
assert 2*27*2==108
full_scalar_real=108
eaten=12
full_transverse=full_scalar_real-eaten
assert full_transverse==96
assert lr_generators*3+full_scalar_real == \
       lr_unbroken*3+lr_broken*4+full_transverse ==156
# A full 5D vector multiplet for 16 L/R generators adds 16 real
# adjoint scalars and 16 symplectic Majorana gauginos (4 per).
# One full 5D hyper in representation 27 adds 2 complex 27 scalars
# (=108 reals) and one 5D Dirac 27 (=108 fermionic units).
bosons=lr_unbroken*3+lr_broken*4+full_transverse+lr_generators
fermions=lr_generators*4+27*4
assert bosons==fermions==172
# At mass-degenerate/identical Wilson characters, periodic free one
# loop cancellation is a DETerminant identity, not merely a count.
# Actual Higgsed multiplet operators and supercharge closure must
# still be constructed; we do NOT assume this condition is paid.
assert bosons-fermions==0

# Full 27 decomposition: each SU3 factor sees one 3-fold 3 and
# one 3-fold bar3. Its cubic parity index cancels for a COMMON
# equal mass sign on all components, unlike a single (3,bar3) Dirac.
rep27=[
    {"c":1,"l":-1,"r":0},  # (3,bar3,1)
    {"c":-1,"l":0,"r":1},  # (bar3,1,3)
    {"c":0,"l":1,"r":-1}   # (1,3,bar3)
]
for factor in ("c","l","r"):
    cubic_index=sum(3*R[factor] for R in rep27)
    assert cubic_index==0
    half_shift=F(cubic_index,2)
    assert half_shift==0
    print(factor, "SU3^3 full 27 pure cubic half-shift",half_shift)
single_bifundamental_L=F(3,2)
single_bifundamental_R=F(-3,2)
assert single_bifundamental_L.denominator==2
assert single_bifundamental_R.denominator==2
# These are necessary LOCAL pure-SU3 conditions, not proof
# of globally well-defined quotient/CS/bordism action.
print("TWO COMPLEX bifundamentals real DOF",36)
print("TWO COMPLEX FULL 27 scalar real DOF",full_scalar_real)
print("Higgsed L/R bosonic units with full 27",156)
print("with adjoint real scalar addition",bosons)
print("one Dirac 27 + 16 adjoint gauginos fermion units",fermions)
print("PASS SU3^3 representation-local cubic 27 cancellation and total vector/hyper field balance")
print("FAIL automatic full E6 source inference from prior 36-real local scalar potential")
print("OPEN common physical gauge/Higgs fermion mass operators, exact 5D SUSY breaking, mixed CS, global vacuum and measured SM")
