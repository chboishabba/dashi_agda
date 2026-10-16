"""Analytic RED/GREEN receipt for the conditional 3D Wannier diagnostics.

This is a synthetic two-band Weyl fixture, not Co1/4TaSe2 evidence.
"""
import numpy as np

import co_tase2_wannier3d_diagnostics as diag

sx = np.array([[0, 1], [1, 0]], complex)
sy = np.array([[0, -1j], [1j, 0]], complex)
sz = np.array([[1, 0], [0, -1]], complex)


def h_and_d(k):
    k = np.asarray(k, float)
    return k[0] * sx + k[1] * sy + k[2] * sz, [sx, sy, sz]


k = np.array([0.31, -0.22, 0.47])
h, d = h_and_d(k)
evals, evecs = np.linalg.eigh(h)

# Lower band of H=k.sigma has Berry curvature -k/(2|k|^3).
omega = diag.berry_curvature_band(evals, evecs, d, 0)
expected = -k / (2 * np.linalg.norm(k) ** 3)
assert np.allclose(omega, expected, rtol=1e-10, atol=1e-10), (omega, expected)

# Lower-band spin points opposite k-hat.
spin = diag.operator_expectations(evecs, [sx, sy, sz])
assert np.allclose(spin[0], -k / np.linalg.norm(k), rtol=1e-10, atol=1e-10)

# Flux through a cube enclosing the Weyl point tends to -2*pi.
flux = diag.berry_flux_cube(
    h_and_d,
    center=np.zeros(3),
    half_width=0.2,
    band_index=0,
    face_n=31,
)
assert abs(flux + 2 * np.pi) < 0.12, flux
assert abs(flux / (2 * np.pi) + 1.0) < 0.02, flux / (2 * np.pi)

# Same-basis SOC interpolation must preserve endpoints and midpoint exactly.
h0 = np.diag([-1.0, 1.0]).astype(complex)
h1 = np.array([[-0.5, 0.2j], [-0.2j, 0.5]], complex)
assert np.allclose(diag.interpolate_same_basis_h(h0, h1, 0.0), h0)
assert np.allclose(diag.interpolate_same_basis_h(h0, h1, 1.0), h1)
assert np.allclose(diag.interpolate_same_basis_h(h0, h1, 0.5), 0.5 * (h0 + h1))

print("WANNIER-3D-WEYL-SELFTEST: PASS", omega.tolist(), flux)
