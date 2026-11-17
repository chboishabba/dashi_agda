#!/usr/bin/env python3
"""Exact rational source-scale negative control for horn gauge acceptance.

CLASSICAL differential-form pullback: under Euclidean dilation x'=s*x
and transported SAME unitary gauge connection, local arclength L'=s*L,
connection coefficient bound M'=M/s, curvature norm K'=K/s**2,
based source-homotopy area H'=s**2*H.
Consequently M'*L'=M*L and K'*H'=K*H. Abstract flat holonomy
is unchanged. This does NOT establish Hatcher source loop geometry or
a real gauge connection; those remain P0/P1.

Attribution: Hatcher original horn topology, prior same-object owner
Agda #1244, selected W owner #1247, unitary norm maxcut #1249/#84.
New source-specific role: avoid falsely treating arbitrary shrinking
of the coordinates as a physical violation of selected W.
"""
from fractions import Fraction as F

for s in (F(1,1000000),F(1,100),F(1,2),F(1),F(2),F(100)):
    M,L,K,H=F(3),F(1,4),F(2,7),F(1,5)
    assert (M/s)*(s*L)==M*L
    assert (K/(s*s))*(s*s*H)==K*H
    assert (M/s)*(s*L)==F(3,4)
print("PASS exact six-scale physical SAME-source ML and curvature-area invariance")

# Requiring identical numerical M under a change of spatial
# scale is a DIFFERENT gauge field, not a passive rescaling.
M,L=F(3),F(1,4)
assert M*(L/F(100)) != M*L
print("PASS false-positive control: freezing M changes source physics")
