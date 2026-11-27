"""Exact Rouche margin from the existing 234446.a1 Mellin interval receipt.
This checks rational bounds only; it does not rerun the earlier quadrature
or prove the complex second derivative zero.
"""
from fractions import Fraction as Q

# Existing B-M7s receipt, outward-rounded at scale 10^-12.
M1 = Q(13, 10**12)
M2 = Q(8270793387711404, 10**12)
r = Q(7, 50_000_000)
# N < 485^2, pi > 3.14, so c = 2*pi/sqrt(N) > 1/80.
c_lower = Q(1, 80)
assertions = [234446 < 485**2, 2*Q(314,100)/485 > c_lower, 0 < r < 1, M2 > 0]
tail = 4/c_lower**2*r**4/(1-r*r)
main = M2*r*r/12
assertions += [M1+tail < main, 12*tail/M2 < Q(2,10**26)]
# A too-small radius fails the same sufficient criterion.
s = Q(1,10**7)
assertions.append(M2*s*s/12 <= M1 + 4/c_lower**2*s**4/(1-s*s))
for i, ok in enumerate(assertions, 1):
    if not ok:
        raise AssertionError(f'central-zero guard {i} failed')
print(f'{len(assertions)}/{len(assertions)} exact rational guards PASS')
print('radius', r, 'margin lower bound', float(main-M1-tail), 'squared-zero error bound',float(12*tail/M2))
