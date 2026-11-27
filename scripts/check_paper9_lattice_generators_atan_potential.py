#!/usr/bin/env python3
"""Exact finite diagnostics only; not Agda acceptance or a limit proof."""
from fractions import Fraction as F
import sympy as s

def square(n):
    return {(a,b) for a in range(-n,n+1) for b in range(-n,n+1)}

def rot(p):
    return p[1], -p[0]

def back(p):
    return -p[1], p[0]

def shear(p):
    return p[0], p[1]+p[0]

def unshear(p):
    return p[0], p[1]-p[0]

checks=0
for n in range(41):
    q,q2,q4=square(n),square(2*n),square(4*n)
    shell=square(n+1)-q
    assert {rot(p) for p in q}==q
    assert {rot(p) for p in shell}==shell
    assert q <= {shear(p) for p in q2} <= q4
    assert all(back(rot(p))==p and unshear(shear(p))==p for p in q2)
    checks+=4
m,k,z=s.symbols("m k z")
assert s.cancel(z*(m*(-1/z)+k)-(k*z-m))==0
assert s.expand(m*(z+1)+k-(m*z+m+k))==0
checks+=2
q=t=F(0)
p=F(1)
total=F(0)
for n in range(400):
    b=2*t+4*q+8*p
    q1,t1,p1=q/2+p,t/2+q,p/2
    assert b==t+2*t1+4*q1+8*p1
    if n%2:
        total+=t/F(n)
        assert total<=8
    q,t,p=q1,t1,p1
    checks+=1
print(f"{checks} exact checks passed (finite lattice, symbolic denominators, rational potential); no kernel execution")
