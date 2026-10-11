from __future__ import annotations

from itertools import product
import numpy as np

F3 = (0, 1, 2)
PAIR_INDICES = {0: (1, 2), 1: (3, 4), 2: (5, 6), 3: (7, 8)}
PHASE_ANGLE = {0: 0.0, 1: 2 * np.pi / 3, 2: 4 * np.pi / 3}


def _dd(f, axis, h):
    return (np.roll(f, -1, axis=axis) - np.roll(f, 1, axis=axis)) / (2 * h)


def _other_two(m):
    return tuple(x for x in F3 if x != m)


def _planes(k, u, v):
    if k == 0:
        return (u, 0), (u, v + 1)
    if k == 1:
        h1, h2 = _other_two(v)
        return (u, h1 + 1), (u, h2 + 1)
    c1, c2 = _other_two(u)
    return (c1, v + 1), (c2, v + 1)


def _basis(nth=7, nz=9):
    th = np.linspace(0, 2 * np.pi, nth, endpoint=False)
    ze = np.linspace(0, 2 * np.pi, nz, endpoint=False)
    TH, ZE = np.meshgrid(th, ze, indexing="ij")
    dth, dze = 2 * np.pi / nth, 2 * np.pi / nz
    B = np.stack([
        np.ones_like(TH), np.cos(TH), np.sin(TH),
        np.cos(3 * ZE), np.sin(3 * ZE),
        np.cos(TH - 3 * ZE), np.sin(TH - 3 * ZE),
        np.cos(TH + 3 * ZE), np.sin(TH + 3 * ZE),
    ], axis=-1)
    Bt = np.stack([
        np.zeros_like(TH), -np.sin(TH), np.cos(TH),
        np.zeros_like(TH), np.zeros_like(TH),
        -np.sin(TH - 3 * ZE), np.cos(TH - 3 * ZE),
        -np.sin(TH + 3 * ZE), np.cos(TH + 3 * ZE),
    ], axis=-1)
    Bz = np.stack([
        np.zeros_like(TH), np.zeros_like(TH), np.zeros_like(TH),
        -3 * np.sin(3 * ZE), 3 * np.cos(3 * ZE),
        3 * np.sin(TH - 3 * ZE), -3 * np.cos(TH - 3 * ZE),
        -3 * np.sin(TH + 3 * ZE), 3 * np.cos(TH + 3 * ZE),
    ], axis=-1)
    return TH, ZE, dth, dze, B, Bt, Bz


def _direction(plane, phase):
    channel, harmonic = plane
    c = np.zeros(27)
    i, j = PAIR_INDICES[harmonic]
    a = PHASE_ANGLE[phase]
    off = channel * 9
    c[off + i] = np.cos(a)
    c[off + j] = np.sin(a)
    return c


def run_replay(nonaxis_floor=0.02):
    TH, ZE, dth, dze, B, Bt, Bz = _basis()
    R0, a0, iota0 = 3.0, 1.0, 0.42

    def metrics(c):
        cr, cz, cs = c[:9], c[9:18], c[18:]
        rho = a0 * (1 + np.tensordot(B, cr, axes=([-1], [0])))
        zoff = a0 * np.tensordot(B, cz, axes=([-1], [0]))
        RR = R0 + rho * np.cos(TH)
        ZZ = rho * np.sin(TH) + zoff
        r = np.stack([RR * np.cos(ZE), RR * np.sin(ZE), ZZ], axis=-1)
        e1, e2 = _dd(r, 0, dth), _dd(r, 1, dze)
        cross = np.cross(e1, e2)
        sg = np.linalg.norm(cross, axis=-1)
        n = cross / sg[..., None]
        ct = 1 + np.tensordot(Bt, cs, axes=([-1], [0]))
        czeta = -iota0 + np.tensordot(Bz, cs, axes=([-1], [0]))
        bth, bze = czeta / sg, -ct / sg
        bv = bth[..., None] * e1 + bze[..., None] * e2
        bm = np.linalg.norm(bv, axis=-1)
        bh = bv / bm[..., None]
        kap = (bth / bm)[..., None] * _dd(bh, 0, dth) + (bze / bm)[..., None] * _dd(bh, 1, dze)
        q = np.cross(n, bh)
        q /= np.linalg.norm(q, axis=-1)[..., None]
        kg = np.sum(kap * q, axis=-1)
        div = (_dd(sg * bth, 0, dth) + _dd(sg * bze, 1, dze)) / sg
        return (
            float(np.std(bm) / np.mean(bm)),
            float(np.sqrt(np.mean(kg * kg))),
            float(np.sqrt(np.mean(div * div))),
            float(np.min(rho)),
            float(np.linalg.norm(c)),
        )

    def score(c):
        br, kg, dv, mr, nm = metrics(c)
        barrier = 0.0 if mr > 0.35 else 300 * (0.35 - mr) ** 2
        return 20 * br ** 2 + 4.5 * kg ** 2 + 50 * dv ** 2 + 0.02 * nm ** 2 + barrier

    amplitudes = np.array([-0.18, -0.12, -0.08, -0.04, 0.04, 0.08, 0.12, 0.18])
    reps = list(product(F3, F3, F3, (0, 1)))
    rows = []

    for k, u, v, relative in reps:
        p, qphase = (0, 0) if relative == 0 else (0, 1)
        pl1, pl2 = _planes(k, u, v)
        d1, d2 = _direction(pl1, p), _direction(pl2, qphase)
        nonaxis = np.array([pl1[1] != 0, pl2[1] != 0], dtype=float)
        best = None
        for a in amplitudes:
            for b in amplitudes:
                if np.linalg.norm(np.array([a, b]) * nonaxis) < nonaxis_floor:
                    continue
                c = a * d1 + b * d2
                s = score(c)
                if best is None or s < best[0]:
                    best = (s, a, b, metrics(c))
        rows.append((best[0], (k, u, v, relative), best[1], best[2], best[3]))

    rows.sort(key=lambda row: row[0])
    best = rows[0]
    return {
        "representative_count": len(rows),
        "nonaxis_floor": nonaxis_floor,
        "best_objective": best[0],
        "best_tag": best[1],
        "best_amplitudes": (best[2], best[3]),
        "best_relative_B_spread": best[4][0],
        "best_geodesic_curvature_rms": best[4][1],
        "best_divergence_rms": best[4][2],
        "best_min_radius_factor": best[4][3],
        "best_coefficient_norm": best[4][4],
    }


if __name__ == "__main__":
    print(run_replay())
