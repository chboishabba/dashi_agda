#!/usr/bin/env python3
"""Exact O(2) inversion of KK circle connection; no forced physical mirror lift."""
import sympy as s
u,a,chi,k,phi=s.symbols('u a chi k phi',nonzero=True,real=True)
theta=u+k*a
theta_prime=(-u+chi)+k*(-a-chi/k)
assert s.expand(theta_prime+theta)==0
assert s.expand(phi**2*theta_prime**2-phi**2*theta**2)==0
Mx=s.diag(-1,1,1)
assert Mx*Mx==s.eye(3) and Mx.det()==-1
print('PASS O(2) KK connection inversion, fibre metric and ternary spatial mirror involution')
