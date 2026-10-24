#!/usr/bin/env python3
"""Dirichlet near-identity recurrences for sibling #1247 SU3 Wilson W.

Original mathematical theorem: compact torus / simultaneous Dirichlet
pigeonhole approximation. Since det(W)=1, two eigenphases suffice;
for every integer Q>=2 there exists 1<=m<=Q^2 with
||W^m-I||op <= 4*pi/Q. Finite-image A5 uniform-gap logic is NOT
transferrable to an infinite-order SU3 cyclic subgroup.
The selected W PMNS rational/ζ parameters belong to Agda PR #1247;
this file is an independently tested numerical regression, not source
of the physical lepton parameters or a horn meridian representation.
"""
from math import pi
import numpy as np
z=np.exp(2j*pi/3)
s12,c12=161/289,240/289
s13,c13=240/1609,1591/1609
s23,c23=20/29,21/29
U=np.array([
 [c12*c13,s12*c13,s13*np.conj(z)],
 [-s12*c23-c12*s23*s13*z,c12*c23-s12*s23*s13*z,s23*c13],
 [s12*s23-c12*c23*s13*z,-c12*s23-s12*c23*s13*z,c23*c13]],complex)
W=np.diag([1,z,z*z])@(2*np.outer(U[:,0],np.conj(U[:,0]))-np.eye(3))
assert np.linalg.norm(W.conj().T@W-np.eye(3),ord=2)<1e-12
assert abs(np.linalg.det(W)-1)<1e-12
vals=np.linalg.eigvals(W)
assert max(abs(abs(t)-1) for t in vals)<1e-12
assert abs(np.prod(vals)-1)<1e-11
print('PASS selected sibling W numerical SU3 unitarity/determinant and eigenphases')
for Q in (4,8,16,32,64,128):
    # Spectral norm of normal W^n-I equals max_i |lambda_i^n-1|.
    powers=np.arange(1,Q*Q+1,dtype=np.int64)
    errs=np.max(abs(np.exp(1j*np.outer(powers,np.angle(vals)))-1),axis=1)
    m=int(np.argmin(errs)+1)
    err=float(errs[m-1])
    assert err<=4*pi/Q+1e-9
    print(f'PASS Q={Q}: some 1<=m={m}<=Q² has ||W^m-I||={err:.10f} <=4π/Q={4*pi/Q:.10f}')
# The observed best first small power is not a theorem about a generic SU3:
assert np.linalg.norm(np.linalg.matrix_power(W,458)-np.eye(3),ord=2)<.045
assert np.linalg.norm(np.linalg.matrix_power(W,458)-np.eye(3),ord=2)>.044
print('PASS selected source near identity at power 458: ||W^458-I||≈0.04449 (NUMERICAL ONLY)')
print('PRIOR THEOREM: two-angle Dirichlet + determinant-one gives m<=Q², epsilon<=4π/Q')
print('NO-GO transferring uniform finite A5 gap to infinite W cyclic group')
print('BOUNDARY near-identity powers alone do not specify which Hatcher descendants carry these powers')
