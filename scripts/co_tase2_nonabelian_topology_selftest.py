"""RED/GREEN regression for degeneracy-safe subspace topology.

Synthetic fixtures only; this is not Co1/4TaSe2 evidence.
"""
import numpy as np

import co_tase2_nonabelian_topology as topo

sx = np.array([[0, 1], [1, 0]], complex)
sy = np.array([[0, -1j], [1j, 0]], complex)
sz = np.array([[1, 0], [0, -1]], complex)


def single_weyl(k):
    k = np.asarray(k, float)
    return k[0] * sx + k[1] * sy + k[2] * sz, [sx, sy, sz]


# Rank-one projector curvature must reproduce the analytic Weyl result.
k = np.array([0.31, -0.22, 0.47])
h, derivs = single_weyl(k)
evals, evecs = np.linalg.eigh(h)
omega = topo.subspace_curvature_vector(evals, evecs, derivs, [0])
expected = -k / (2 * np.linalg.norm(k) ** 3)
assert np.allclose(omega, expected, rtol=1e-10, atol=1e-10), (omega, expected)

# Two exactly degenerate copies exercise a genuine rank-two occupied subspace.
h2 = np.kron(np.eye(2), h)
d2 = [np.kron(np.eye(2), d) for d in derivs]
e2, u2 = np.linalg.eigh(h2)
omega2 = topo.subspace_curvature_vector(e2, u2, d2, [0, 1])
assert np.allclose(omega2, 2 * expected, rtol=1e-10, atol=1e-10), (omega2, 2 * expected)

# Curvature must be invariant under arbitrary gauge rotations inside the selected
# and complementary degenerate subspaces.
rng = np.random.default_rng(7)
def unitary(n):
    q, r = np.linalg.qr(rng.normal(size=(n, n)) + 1j * rng.normal(size=(n, n)))
    phase = np.diag(r)
    return q @ np.diag(np.where(np.abs(phase) > 0, phase / np.abs(phase), 1.0))
rot = np.eye(4, dtype=complex)
rot[:2, :2] = unitary(2)
rot[2:, 2:] = unitary(2)
u2g = u2 @ rot
omega2g = topo.subspace_curvature_vector(e2, u2g, d2, [0, 1])
assert np.allclose(omega2g, omega2, rtol=1e-10, atol=1e-10), (omega2g, omega2)

# Selection must fail closed if the chosen subspace is not spectrally isolated.
try:
    topo.subspace_curvature_vector(np.array([-1.0, 0.0, 0.0, 1.0]), np.eye(4),
                                   [np.eye(4)] * 3, [0, 1], gap_floor=1e-8)
    raise AssertionError("non-isolated subspace was accepted")
except ValueError as exc:
    assert "isolated" in str(exc).lower() or "gap" in str(exc).lower()

# SSH equatorial loop has a pi Berry phase for the lower band. Wilson-loop
# eigenphases are gauge invariant modulo 2*pi.
frames = []
for q in np.linspace(0.0, 2 * np.pi, 241, endpoint=False):
    hh = np.cos(q) * sx + np.sin(q) * sy
    ee, uu = np.linalg.eigh(hh)
    frames.append(uu[:, [0]])
phases = topo.wilson_loop_phases(frames)
assert phases.shape == (1,)
assert abs(abs(phases[0]) - np.pi) < 2e-3, phases

# An explicitly k-dependent phase gauge may choose +pi instead of -pi, so compare
# Wilson eigenvalues on U(1), not principal-angle representatives on R.
frames_g = [f * np.exp(1j * (0.37 * i + 0.013 * i * i))
            for i, f in enumerate(frames)]
phases_g = topo.wilson_loop_phases(frames_g)
assert np.allclose(
    np.sort_complex(np.exp(1j * phases_g)),
    np.sort_complex(np.exp(1j * phases)),
    atol=1e-10,
), (phases_g, phases)

print("NONABELIAN-TOPOLOGY-SELFTEST: PASS", omega.tolist(), omega2.tolist(), phases.tolist())
