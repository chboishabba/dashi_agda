#!/usr/bin/env python3
"""YM M.03/M.05 physical rate scaling negative/positive reference only."""
from decimal import Decimal, getcontext
getcontext().prec=65
ln2=Decimal(2).ln()
m=Decimal("1.5")
r=Decimal(1)
for k in (1,2,4,8,12,16):
    a=Decimal(1)/(Decimal(2)**k)
    lattice_distance=int(r/a)
    q_fixed=Decimal("0.5")
    q_scaled=(-m*a).exp()
    rate_fixed=-q_fixed.ln()/a
    rate_scaled=-q_scaled.ln()/a
    assert abs(rate_fixed-ln2/a)<Decimal("1e-55")
    assert abs(rate_scaled-m)<Decimal("1e-55")
    assert abs(q_scaled**lattice_distance-(-m*r).exp())<Decimal("1e-55")
print("PASS fixed q=1/2 yields envelope physical rate ln2/a, divergent")
print("PASS q(a)=exp(-ma) yields constant finite physical envelope rate m")
print("NOTE an upper envelope does not prove spectral nontriviality or exact mass")
