#!/usr/bin/env python3
"""Exact rational NV five-state steady-state fixture + TSFV coarse-observation loss.

A mathematical generator fixture with positive rates, not experimental NV
parameters. TSFV history non-identifiability is not evidence for time-symmetric
quantum mechanics, retrocausality, or biological memory effects.
"""
import sympy as s
# states g0,g1,e0,e1,s; destination rows, source columns
Q=s.zeros(5)
edges=[(0,2,3),(1,3,3),(2,0,4),(3,1,4),
       (2,4,1),(3,4,2),(4,0,3),(4,1,1),
       (0,1,1),(1,0,1)]
for i,j,k in edges:
    Q[j,i]+=k
    Q[i,i]-=k
assert all(sum(Q[:,j])==0 for j in range(5))
A=Q.copy()
A[4,:]=s.ones(1,5)
b=s.Matrix([0,0,0,0,1])
stationary=A.inv()*b
assert Q*stationary==s.zeros(5,1)
assert sum(stationary)==1
assert all(a>0 for a in stationary)
eta0,eta1,bg=s.symbols("eta0 eta1 bg",nonnegative=True,real=True)
photon=eta0*4*stationary[2]+eta1*4*stationary[3]+bg
assert s.simplify(photon.subs({eta0:0,eta1:0})-bg)==0
# Same coarse observed count does not identify histories ABC and ACB:
photon_ABC=photon_ACB=photon
assert photon_ABC==photon_ACB
print("PASS rational 5-level steady-state fixture, positive populations, unit mass")
print("stationary =", list(stationary))
print("photon mean =", photon)
print("TSFV: coarse photon mean is non-injective on distinct ordered histories")
print("SCOPE: no calibrated NV rates, detector process, or quantum TSFV phase")
