#!/usr/bin/env python3
"""Exact sibling-density, curvature-budget, and necessary gauge-growth audit.

SOURCE ROOTS: Hatcher, Algebraic Topology Ex. 2B.2 (marked free-group
commutator tower); Gotô, JMSJ 1949 (compact semisimple commutators).
EXISTING PR OWNERS: Agda #1247 selected SU(3) W and abstract positive
representation; Agda #1244 actual 3-sector gluing; Agda #1249 / Lean #84
prior single-branch and sibling-adaptive inequalities.

NEW: a finite 3-level two-short-siblings certificate, sparse-density
product test, source-conditional necessary growth for gauge coefficients,
and an exact maximal Stokes-curvature budget. This is exact FINITE
arithmetic, NOT a Hatcher spatial embedding or theorem-prover receipt.
"""
from fractions import Fraction as F
from itertools import combinations

CERT_ROOT_GAP_SQ = F(854996726408, 648677790003)
assert CERT_ROOT_GAP_SQ > 1


def amp(gap):
    assert F(0) <= gap <= 2
    return 2 * min(F(1), gap)


def envelope(gaps, errors, leaf=F(2)):
    assert len(gaps) == len(errors)
    assert F(0) <= leaf <= 2
    assert all(e >= 0 for e in errors)
    out = leaf
    for gap, error in reversed(list(zip(gaps, errors))):
        out = error + amp(gap) * out
    return out


def coefficients(gaps):
    prefix = F(1)
    out = []
    for gap in gaps:
        out.append(prefix)
        prefix *= amp(gap)
    return out, prefix


# Initial depth-three marked branch with ANY TWO sibling gaps <=1/4,
# and the third arbitrary unitary gap <=2, has root gap <=1.
for small in combinations(range(3), 2):
    gaps = [F(1, 4) if k in small else F(2) for k in range(3)]
    assert envelope(gaps, [F(0)] * 3) == 1
# PRODUCT-ONLY depth-three negative control: a single short sibling can
# still certify rejection via the EXISTING shorter-depth linear sibling bound.
# See check_horn_optimal_sibling_stopping_tail.py; no blanket one-short no-go.
assert envelope([F(1, 4), F(2), F(2)], [F(0)] * 3) == 4
print('PASS product-only 3-stage TWO small siblings; shorter one-sibling stops may be sharper')

# Sparse density, arbitrary placement: >=2m of first 3m gaps <=1/4
# forces flat d(root)<=2^(1-m), independent of selected leaf length.
for m in range(1, 9):
    n = 3*m
    gap = [F(1, 4)] * (2*m) + [F(2)] * m
    assert envelope(gap, [F(0)]*n) == F(2)**(1-m)
    assert envelope(list(reversed(gap)), [F(0)]*n) == F(2)**(1-m)
print('PASS all prefix sparse-density bounds at m=1..8 (2 good of every 3 aggregate)')

# GENUINE geometrically marked sibling length hypothesis L_k<=L0*q^k.
# With a uniform source-compatible bound M:
# d(root)<=2*(2*M*L0)^n*q^(n(n-1)/2).
M, L0, q = F(3), F(1, 3), F(3, 4)
for n in range(1, 20):
    gap = [min(F(2), M*L0*q**k) for k in range(n)]
    upper = 2*(2*M*L0)**n*q**(n*(n-1)//2)
    assert envelope(gap, [F(0)]*n) <= upper
assert envelope([q**k for k in range(7)], [F(0)]*7) < 1
assert envelope([q**k for k in range(6)], [F(0)]*6) > 1
print('PASS length-source conditional: q=3/4 M=3 L0=1/3 first cut depth 7')

# NECESSARY source growth: if selected root d(W)>1, FLAT holonomy
# implies (2*M_n*L0)^n*q^(n(n-1)/2) > 1/2,
# where M_n=max sup||A|| over the first n correctly marked siblings.
for n in (1, 3, 7, 12, 20):
    lhs = (2*M*L0)**n * q**(n*(n-1)//2)
    if lhs <= F(1,2):
        assert 2*lhs <= 1
    print('source growth n=', n, 'M=3 admissible?', lhs > F(1,2),
          'necessary polynomial lhs=', str(lhs))

# CURVED non-Abelian Stokes strips must produce actual eta_k.
# Synthetic eta_k<=K*A0*r^k, A0=1, r=1/2.
# Largest K from an exact finite depth-n <=1 budget:
# Kcrit=(1-2*product(c_k))/(sum_j prefix(c)_j*r^j).
for n in (7, 8, 10, 12):
    gap = [q**k for k in range(n)]
    prefixes, P = coefficients(gap)
    area_sum = sum((prefixes[k]*F(1,2)**k for k in range(n)), F(0))
    Kcritical = (1-2*P)/area_sum
    assert Kcritical > 0
    assert envelope(gap, [Kcritical*F(1,2)**k for k in range(n)]) == 1
    assert envelope(gap, [F(1,100)*F(1,2)**k for k in range(n)]) < 1
    assert envelope(gap, [(Kcritical+1)*F(1,2)**k for k in range(n)]) > 1
    print('PASS exact depth', n, 'curvature cap numerator/denominator', Kcritical)

print('OPEN: actual Hatcher / 3-satellite source geometric loop lengths, clearance, and curvature strips')
print('NO CLAIM: real SU3 field, selected experimental holonomy, local gauge blow-up exponent, or kernel theorem')
