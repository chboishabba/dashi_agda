#!/usr/bin/env python3
"""K27/26D: SU2 WZW S3 global H gerbe, explicit dual C22, modular control.

PRIOR ART: WZW flux quantization, SU(2)_k Sugawara CFT and bosonic
spacelike linear dilaton. Exact symbolic/rational checks; modular
matrix tests are 50-digit NUMERICAL, not new modularity proofs.
No K27 nonlinear generator, physical BRST, 369 or Monster intertwiner.
"""
from fractions import Fraction as F
import sympy as sp
from mpmath import mp

chi, theta, varphi, x, aprime, r = sp.symbols(
    'chi theta varphi x alphaPrime r', real=True, positive=True)
fchi = chi - sp.sin(2 * chi) / 2
area2 = sp.sin(theta)
h = 2 * r**2 * sp.sin(chi)**2 * area2
north = r**2 * fchi * area2
south = r**2 * (fchi - sp.pi) * area2
assert sp.simplify(sp.diff(north, chi) - h) == 0
assert sp.simplify(sp.diff(south, chi) - h) == 0
assert sp.simplify(north - south - sp.pi * r**2 * area2) == 0
assert north.subs(chi, 0) == 0 and south.subs(chi, sp.pi) == 0
flux = sp.integrate(h, (chi, 0, sp.pi), (theta, 0, sp.pi),
                    (varphi, 0, 2 * sp.pi))
assert sp.simplify(flux - 4 * sp.pi**2 * r**2) == 0
assert sp.simplify(sp.integrate(north - south,
                 (theta, 0, sp.pi), (varphi, 0, 2 * sp.pi)) - flux) == 0
print('PASS S3 B_N and B_S potentials, common H, overlap and 4pi²r² flux')
for k in range(1, 21):
    assert sp.simplify(
        (flux / (4 * sp.pi**2 * aprime)).subs(r**2, k * aprime)) == k
print('PASS 20 integral WZW flux levels: k=r²/alphaPrime (semiclassical scheme)')
# Global B is impossible when k != 0; overlap 2-form is non-exact on S2.
# Proper object is a gerbe, not a single globally defined gauge one-form.

# Orientation: vol26=vol(R1,22) ^ vol(S3), H=+2/r vol(S3),
# so *26H = -2/r vol(R1,22) for mostly-plus metric.
# beta22=dt ^ dx2 ^ .. ^ dx22, dx1 ^ beta22=-vol(R1,22).
# Choose C22=-exp(-2Phi)*beta22; its derivative is G23=e^-2Phi*H.
phi = x / r
c22_coeff = -sp.exp(-2 * phi)
g23_coeff = -sp.diff(c22_coeff, x)
hodge_expected = -(2 / r) * sp.exp(-2 * phi)
assert sp.simplify(g23_coeff - hodge_expected) == 0
assert (-1)**(3 * 23 + 1) == 1  # Lorentzian star^2 on 3/23-forms.
assert sp.simplify(sp.exp(2 * phi) * g23_coeff + 2 / r) == 0
print('PASS global dual C22 on noncompact R1,22: dC=e^-2Phi *26H')

for k in range(1, 21):
    q = F(1, k + 2)
    c = F(3 * k, k + 2)
    assert 23 + 6 * q + c == 26
    assert F(6, k) + 23 + c - 26 == F(12, k * (k + 2))
    assert F(6, k) - 4 * q - F(2, k) == F(8, k * (k + 2))
print('PASS 20 exact finite-level central-charge and classical beta residuals')

labels = 0
for k in range(1, 16):
    for ell in range(k + 1):
        j = F(ell, 2)
        assert j * (j + 1) / F(k + 2) == F(
            ell * (ell + 2), 4 * (k + 2))
        labels += 1
assert labels == 135
print('PASS 135 rational SU2_k integrable primary weights, k=1..15')

# SOURCE modular matrices: high-precision regression, not a theorem.
mp.dps = 50
for k in range(1, 13):
    n = k + 1
    sm = mp.matrix([
        [mp.sqrt(mp.mpf(2) / (k + 2)) *
         mp.sin(mp.pi * (i + 1) * (j + 1) / (k + 2))
         for j in range(n)] for i in range(n)])
    c = mp.mpf(3 * k) / (k + 2)
    tm = mp.matrix(n)
    for i in range(n):
        hw = mp.mpf(i * (i + 2)) / (4 * (k + 2))
        tm[i, i] = mp.e ** (2j * mp.pi * (hw - c / 24))
    sq = sm * sm
    cube = (sm * tm)**3
    identity = mp.eye(n)
    err = max(
        [abs(sq[i, j] - identity[i, j])
         for i in range(n) for j in range(n)] +
        [abs(cube[i, j] - sq[i, j])
         for i in range(n) for j in range(n)])
    assert err < mp.mpf('1e-42'), (k, err)
print('PASS SU2_k modular S²=I and (ST)³=S², levels 1..12, 50-digit numerical')
print('BOUNDARY SU2 affine modular matrices != noncompact full string partition function/BRST')
print('BOUNDARY classical k geometry and quantum k+2 charge require alpha-prime matching')
