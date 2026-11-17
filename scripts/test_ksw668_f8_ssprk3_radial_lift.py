#!/usr/bin/env python3
"""Exact original three-stage SSPRK3 scaling with time-varying coefficients.

Algebraic source/field reconstruction only; NOT coupled radial-normal
energy, CFL, numerical convergence or Agda kernel acceptance.
"""
from fractions import Fraction as F
import random
rng=random.Random(6683703)
def euler(y,dt,a,src):return y+dt*(a*y+src)
def ssprk3(y,dt,a0,a1,a2,s0,s1,s2):
    y1=euler(y,dt,a0,s0)
    y2=F(3,4)*y+F(1,4)*euler(y1,dt,a1,s1)
    return F(1,3)*y+F(2,3)*euler(y2,dt,a2,s2)
checks=0
for _ in range(250):
    y,dt,a0,a1,a2,s0,s1,s2,lam=[F(rng.randrange(-12,13),rng.randrange(1,10)) for _ in range(9)]
    assert ssprk3(lam*y,dt,a0,a1,a2,lam*s0,lam*s1,lam*s2)==lam*ssprk3(y,dt,a0,a1,a2,s0,s1,s2)
    checks+=1
print(f"{checks}/{checks} exact time-varying SSPRK3 reconstruction checks PASS")
