from __future__ import annotations

from itertools import product
from math import pi
from typing import Dict, List, Tuple

import numpy as np

F3 = (0, 1, 2)

# Harmonic families used by the current Phase243 search chart:
#   0: theta
#   1: 3 zeta
#   2: theta - 3 zeta
#   3: theta + 3 zeta
#
# A discrete torus translation is encoded by (a,b) in F3^2 with
#   Delta theta = 2*pi*a/3
#   Delta zeta  = 2*pi*b/9.
# Its phase shift on the four families is therefore
#   a, b, a-b, a+b  (mod 3).


def phase_shift(harmonic: int, a: int, b: int) -> int:
    if harmonic == 0:
        return a % 3
    if harmonic == 1:
        return b % 3
    if harmonic == 2:
        return (a - b) % 3
    if harmonic == 3:
        return (a + b) % 3
    raise ValueError(harmonic)


def _other_two(missing: int) -> Tuple[int, int]:
    xs = [x for x in F3 if x != missing]
    return xs[0], xs[1]


def selected_harmonics(k: int, u: int, v: int) -> Tuple[int, int]:
    if k == 0:
        return 0, v + 1
    if k == 1:
        h1, h2 = _other_two(v)
        return h1 + 1, h2 + 1
    if k == 2:
        return v + 1, v + 1
    raise ValueError(k)


def canonical_advance_translation(k: int, u: int, v: int) -> Tuple[int, int]:
    """Canonical coordinate translation implementing p,q -> p+1,q+1.

    The chart uses cos(phi) cos(H) + sin(phi) sin(H) = cos(H-phi).
    Thus increasing the coefficient phase by +2*pi/3 is realized by a
    coordinate pullback whose harmonic phase shift is -1 == 2 mod 3.
    """
    h1, h2 = selected_harmonics(k, u, v)
    solutions = [
        (a, b)
        for a, b in product(F3, repeat=2)
        if phase_shift(h1, a, b) == 2 and phase_shift(h2, a, b) == 2
    ]
    if not solutions:
        raise AssertionError((k, u, v, h1, h2))
    return min(solutions)


def _arg(harmonic: int, theta, zeta):
    if harmonic == 0:
        return theta
    if harmonic == 1:
        return 3 * zeta
    if harmonic == 2:
        return theta - 3 * zeta
    if harmonic == 3:
        return theta + 3 * zeta
    raise ValueError(harmonic)


def _line(harmonic: int, phase: int, theta, zeta):
    return np.cos(_arg(harmonic, theta, zeta) - 2 * pi * phase / 3)


def verify() -> Dict[str, object]:
    incidences: List[Tuple[int, ...]] = []
    for k, u, v in product(F3, repeat=3):
        h1, h2 = selected_harmonics(k, u, v)
        a, b = canonical_advance_translation(k, u, v)
        assert phase_shift(h1, a, b) == 2
        assert phase_shift(h2, a, b) == 2
        incidences.append((k, u, v, h1, h2, a, b))

    theta = np.linspace(0.0, 2 * pi, 31, endpoint=False)
    zeta = np.linspace(0.0, 2 * pi, 37, endpoint=False)
    TH, ZE = np.meshgrid(theta, zeta, indexing="ij")

    max_advance_error = 0.0
    max_inverse_error = 0.0
    state_count = 0

    for k, u, v, p, q in product(F3, repeat=5):
        state_count += 1
        h1, h2 = selected_harmonics(k, u, v)
        a, b = canonical_advance_translation(k, u, v)
        dtheta = 2 * pi * a / 3
        dzeta = 2 * pi * b / 9

        # Pulling coordinates back by the canonical translation exactly
        # reproduces simultaneous coefficient-phase advance.
        for h, phase in ((h1, p), (h2, q)):
            translated = _line(h, phase, TH + dtheta, ZE + dzeta)
            advanced = _line(h, (phase + 1) % 3, TH, ZE)
            max_advance_error = max(
                max_advance_error,
                float(np.max(np.abs(translated - advanced))),
            )

            # Spatial reflection (theta,zeta)->(-theta,-zeta) realizes
            # coefficient-phase inversion p->-p.
            reflected = _line(h, phase, -TH, -ZE)
            inverted = _line(h, (-phase) % 3, TH, ZE)
            max_inverse_error = max(
                max_inverse_error,
                float(np.max(np.abs(reflected - inverted))),
            )

    assert len(incidences) == 27
    assert state_count == 243
    assert max_advance_error < 1e-12
    assert max_inverse_error < 1e-12

    return {
        "incidence_count": len(incidences),
        "state_count": state_count,
        "all_incidence_shifts_solved": True,
        "incidences": incidences,
        "max_advance_error": max_advance_error,
        "max_inverse_error": max_inverse_error,
    }


if __name__ == "__main__":
    print(verify())
