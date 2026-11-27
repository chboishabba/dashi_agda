#!/usr/bin/env python3
"""Exact rational replay of the finite inequalities in SharpRadius/Root.
No analytic same-object claim and no Agda acceptance claim.
Run from any directory; reads the committed native literals.
"""
from fractions import Fraction as F
from math import factorial
from pathlib import Path
import re

root = Path(__file__).resolve().parents[1] / "DASHI/Moonshine"
def literals(name):
    source = (root / (name + ".agda")).read_text()
    return {k: F(int(a), int(b)) for k, a, b in
            re.findall(r"^(\w+) = \+ (\d+) / (\d+)$", source, re.M)}

a = literals("JInvariantBishopCM163SharpRadiusExact")
b = literals("JInvariantBishopCM163SharpRootEnclosureExact")
p, P, s, S, x, X, e, E, r, R = (
    a[k] for k in ("piL", "piU", "sqrtL", "sqrtU", "xL", "xU",
                   "eL", "eU", "rL", "rU"))
eps, cl, cu = (b[k] for k in ("eps", "cl", "cu"))
K = 262537412640768000

def atan32(z):
    return sum(((-1)**k * z**(2*k+1) / (2*k+1)
                for k in range(32)), F(0))

def exp32(z):
    return sum((z**k / factorial(k) for k in range(32)), F(0))

stage = 16*atan32(F(1, 5)) - 4*atan32(F(1, 239))
err = F(4, 25**32)
xl = 1-240*R+2160*r*r-eps
xu = 1-240*r+2160*R*R+eps
yl = 1+504*r-16632*R*R-eps
yu = 1+504*R-16632*r*r+eps
dl, du = yl*yl-xu**3, yu*yu-xl**3
checks = {
    "Machin lower": p <= stage-err,
    "Machin upper": stage+err <= P,
    "sqrt lower": s*s <= 163,
    "sqrt upper": 163 <= S*S,
    "scaled exponent lower": x <= p*s/64,
    "scaled exponent upper": P*S/64 <= X,
    "Taylor ratio domain": 0 <= x <= X <= 1,
    "exp lower": e <= exp32(x),
    "exp upper": exp32(X)+F(16,15)*X**32/factorial(32) <= E,
    "radius lower": E**64*r <= 1,
    "radius upper": 1 <= e**64*R,
    "E4 tail": F(16,15)*240*3**4*R**3 <= eps,
    "E6 tail": F(16,15)*504*3**6*R**3 <= eps,
    "positive intervals": 0 < xl <= xu and 0 < yl <= yu,
    "positive discriminant magnitude": 0 < dl <= du,
    "negative j lower": du*cl <= 1728*xl**3,
    "negative j upper": 1728*xu**3 <= dl*cu,
    "literal half-unit": cl == K-F(1,2) and cu == K+F(1,2),
}
for name, ok in checks.items():
    print(f"{'PASS' if ok else 'FAIL'} {name}")
if not all(checks.values()):
    raise SystemExit(1)
lo, hi = K-1728*xu**3/dl, K-1728*xl**3/du
assert -F(1,2) <= lo <= hi <= F(1,2)
print(f"offset diagnostic: [{float(lo):.12e}, {float(hi):.12e}]")
print(f"{len(checks)} exact rational inequalities passed; kernel not run")
