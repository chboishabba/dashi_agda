"""P63/mmc (#194) Co 2a A-type magnetic Seitz/Bloch validator.
Scientific boundary: symmetry-compatible FOUR-band toy, not a DFT/ARPES fit.
Requires gemmi, numpy.  BNS metadata: P6_3'/m'm'c (#194.268), Hall -P 6c' 2c.
Sources: DOI 10.1103/PhysRevB.110.144420 and 10.1038/s41467-026-76784-x.
"""
import json
from math import pi

import gemmi
import numpy as np

BNS_NUMBER = "194.268"
BNS_SYMBOL = "P6_3'/m'm'c"
MAGNETIC_HALL = "-P 6c' 2c"
sg = gemmi.find_spacegroup_by_name("P 63/m m c")
sites = (np.array([0., 0., 0.]), np.array([0., 0., .5]))
moments = (1, -1)


def operations():
    out = []
    for op in sg.operations():
        R = np.asarray(op.rot, dtype=int) // 24
        t = np.asarray(op.tran, dtype=float) / 24
        axial = int(round(np.linalg.det(R) * R[2, 2]))
        targets, shifts, tags = [], [], []
        for a, p in enumerate(sites):
            x = R @ p + t
            b = next((i for i, q in enumerate(sites)
                      if np.allclose(x-q, np.rint(x-q))), None)
            if b is None:
                raise ValueError(("site not mapped", op.triplet()))
            targets.append(b)
            shifts.append(np.rint(x-sites[b]).astype(int))
            tags.append(moments[a]*moments[b]*axial)
        assert tags[0] == tags[1]
        out.append((op.triplet(), R, t, tuple(targets), shifts,
                    axial, tags[0] == -1))
    assert len(out) == 24 and sum(g[-1] for g in out) == 12
    return out


OPS = operations()


def k_transform(g, k):
    return (-1 if g[-1] else 1) * np.linalg.solve(g[1].T, k)


def sewing(g, k):
    kp = k_transform(g, k)
    U = np.zeros((4, 4), complex)
    for a in range(2):
        b = g[3][a]
        phase = np.exp(-2j*pi*np.dot(kp, g[4][a]))
        flip = g[5] * (-1 if g[6] else 1) == -1
        for s in range(2):
            U[2*b+(1-s if flip else s), 2*a+s] = phase
    return U


def compose_index(g1, g2):
    """Find canonical representative of {R1|t1}{R2|t2}, including T parity."""
    R = g1[1] @ g2[1]
    t = g1[1] @ g2[2] + g1[2]
    anti = bool(g1[6]) ^ bool(g2[6])
    matches = []
    for i, g in enumerate(OPS):
        if g[6] != anti or not np.array_equal(g[1], R):
            continue
        delta = t - g[2]
        if np.allclose(delta, np.rint(delta)):
            matches.append((i, np.rint(delta).astype(int)))
    if len(matches) != 1:
        raise AssertionError(("non-unique composition", g1[0], g2[0], matches))
    return matches[0]


def _scalar_gauge_equivalent(left, right, atol=1e-10):
    q = left @ right.conj().T
    phase = q[0, 0]
    return abs(abs(phase)-1) < atol and np.allclose(q, phase*np.eye(4), atol=atol)


def verify_sewing_cocycle(k):
    tests = 0
    for g1 in OPS:
        for g2 in OPS:
            g3_index, _lattice_shift = compose_index(g1, g2)
            g3 = OPS[g3_index]
            U1 = sewing(g1, k_transform(g2, k))
            U2 = sewing(g2, k)
            # If the left operator is antiunitary it conjugates the second
            # sewing matrix before multiplication.
            product = U1 @ (U2.conj() if g1[6] else U2)
            if not _scalar_gauge_equivalent(product, sewing(g3, k)):
                raise AssertionError(("sewing cocycle", g1[0], g2[0], g3[0], k.tolist()))
            tests += 1
    return tests


def harmonic(k, character=False):
    n = np.array([1, 2, 3])
    return sum(((-1 if g[3][0] else 1) if character else 1)
               * np.cos(2*pi*np.dot(k, g[1] @ n))
               for g in OPS)/24


def H(k, J=.7, coupling=.2):
    e = harmonic(k)
    d = coupling*harmonic(k, True)
    return np.diag([e+J+d, e-J-d, e-J+d, e+J-d]).astype(complex)


def verify():
    rng = np.random.default_rng(14)
    covariance = 0
    cocycle = 0
    for k in rng.uniform(-.4, .4, size=(16, 3)):
        for g in OPS:
            U = sewing(g, k)
            assert np.allclose(U.conj().T @ U, np.eye(4))
            transformed = U @ (H(k).conj() if g[6] else H(k)) @ U.conj().T
            assert np.allclose(transformed, H(k_transform(g, k)), atol=1e-10), g[0]
            covariance += 1
        cocycle += verify_sewing_cocycle(k)
    for kz in (0., .5):
        for x, y in rng.uniform(-.4, .4, size=(16, 2)):
            eigen = np.diag(H(np.array([x, y, kz]))).real
            assert np.allclose(sorted(eigen[[0, 2]]), sorted(eigen[[1, 3]]))
    assert abs(harmonic(np.array([.129, .237, .267]), True)) > 1e-8
    return {
        "bns_number": BNS_NUMBER,
        "bns_symbol": BNS_SYMBOL,
        "magnetic_hall_symbol": MAGNETIC_HALL,
        "nuclear_space_group": sg.xhm(),
        "nuclear_ops": len(OPS),
        "antiunitary_ops": sum(g[6] for g in OPS),
        "bloch_covariance_tests": covariance,
        "sewing_cocycle_tests": cocycle,
        "nodal_tests": 32,
        "status": "symmetry toy with cocycle receipt; literal independent magCIF and material Hamiltonian still required",
    }


if __name__ == "__main__":
    print(json.dumps(verify(), indent=2))
