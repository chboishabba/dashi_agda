#!/usr/bin/env python3
"""Exact finite toy transfer-operator composition vs false scalar T-product.
Not the CMP119 physical T or original SU(N) Haar source.
Demonstrates an interface hazard in identifying operator T^(j) with scalar
oneStepValue of CMP119 Eq(2.18) without intermediate-state contractions.
"""
import sympy as sp
s,t=sp.symbols('s t')
A=sp.Matrix([[2,1],[1,3]])
B=sp.Matrix([[3,2],[1,2]])
F=sp.diag(0,2)
G=sp.diag(2,0)
left=sp.Matrix([[1,0]])
right=sp.Matrix([1,1])
Id=sp.eye(2)
K=sp.expand((left*A*(Id+s*F)*B*(Id+t*G)*right)[0])
coeff=lambda P:(P.coeff(s,0).coeff(t,0),P.coeff(s,1).coeff(t,0),P.coeff(s,0).coeff(t,1),P.coeff(s,1).coeff(t,1))
assert coeff(K)==(13,6,14,4)
assert K==13+6*s+14*t+4*s*t
# Full finite intermediate-state sequence expansion is exact; the sum over
# index b is essential, rather than multiplication of two separately summed T masses.
expanded=sp.expand(sum(left[0,a]*A[a,b]*(1+s*F[b,b])*B[b,c]*(1+t*G[c,c])*right[c]
                       for a in range(2) for b in range(2) for c in range(2)))
assert expanded==K
scalar_product=sp.expand((left*A*(Id+s*F)*right)[0]*(left*B*(Id+t*G)*right)[0])
assert scalar_product==15+10*s+18*t+12*s*t
assert coeff(K)!=coeff(scalar_product)
# Both are positive-mark source polynomials, so even the sharp moment cone cannot
# establish equality of the underlying ordered physical T operations.
def cone(c):
    z,f,g,h=c
    return 0<=f<=2*z and 0<=g<=2*z and max(0,2*f+2*g-4*z)<=h<=min(2*f,2*g)
assert cone(coeff(K)) and cone(coeff(scalar_product))
# Interchange test: operations in general don't commute.
assert A*B!=B*A
assert sp.expand((left*B*(Id+s*F)*A*(Id+t*G)*right)[0]) != K
# Correct scalarized expansion: the common intermediate label must be kept.
per_intermediate=[sp.expand(sum(left[0,a]*A[a,b]*(1+s*F[b,b])*B[b,c]*(1+t*G[c,c])*right[c]
                                for a in range(2) for c in range(2))) for b in range(2)]
assert sp.expand(sum(per_intermediate))==K
print('PASS exact ordered T-like contraction: K=13+6s+14t+4st')
print('PASS false independently scalarized product: 15+10s+18t+12st')
print('PASS both coefficient vectors satisfy positive F19 moment cone; cone does not identify T')
print('PASS retain intermediate-state sum and ordering; neither operator commutation nor scalar factorization assumed')
print('NO physical CMP119 T^(j), no SU(N) Haar/Wilson, no RG or Clay gap claimed')
