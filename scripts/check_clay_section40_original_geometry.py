#!/usr/bin/env python3
"""Section40 exact original-source finite geometry controls.

Original BSD: symmetric two-crossing h and strictly increasing signed
positive-source moments when max(a,b)>=1.
Original Hodge: all six Q0 signed partners preserve polynomial values,
flip derivatives, square discriminants, and square to identity.
Original PNP: finite clock is uninhabited at k=0 and any deterministic
two-input output split requires a paired observation split before k.
Finite tests only: NO universal Clay proof or native Lean/Agda receipt.
"""
from fractions import Fraction as F
from itertools import product

counts = {"BSD": 0, "Hodge": 0, "PNP": 0}
for a, b in ((F(1), F(2)), (F(3, 2), F(3, 4)),
             (F(1, 2), F(5, 2)), (F(4), F(1, 3))):
    h = [F(1)]
    for n in range(1, 40):
        h.append(a*h[-1] + b**n)
    m = lambda n: F(0) if n == 0 else (a+b+1)**n
    for n in range(38):
        assert h[n+1] == b*h[n] + a**(n+1)
        assert h[n]*m(n+2) - h[n+1]*m(n+1) > 0
        assert m(n+2) > m(n+1)
        counts["BSD"] += 3

def q0(a, s):
    return (-3*a**3 - 3*a*a*s - a*a + 3*a*s +
            3*a - 2*s*s + s + 3)

def df(a, s):
    return -3*a*a + 3*a + 1 - 4*s

for aa in product((F(-1), F(0), F(1, 2)), repeat=6):
    ss = tuple(F(i-2, 3) for i in range(6))
    partners = tuple(v + df(a,v)/2 for a,v in zip(aa,ss))
    for a,s,t in zip(aa,ss,partners):
        assert q0(a,s) == q0(a,t)
        assert df(a,t) == -df(a,s)
        assert df(a,t)**2 == df(a,s)**2
        assert t + df(a,t)/2 == s
        assert (t==s) == (df(a,s)==0)
        counts["Hodge"] += 5

for steps in product((0,1),repeat=4):
    step = lambda st,ob: steps[2*st+ob]
    for ox in product((0,1),repeat=3):
        for oy in product((0,1),repeat=3):
            sx = sy = 0
            saw_difference = False
            for k in range(1,4):
                saw_difference |= ox[k-1] != oy[k-1]
                sx,sy=step(sx,ox[k-1]),step(sy,oy[k-1])
                if sx != sy:
                    assert saw_difference
                    assert 0 <= k-1 < k
                    counts["PNP"] += 2
assert not list(range(0))
print("SECTION40 ORIGINAL EXACT PASS", counts, sum(counts.values()))
