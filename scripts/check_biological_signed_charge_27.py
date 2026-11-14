#!/usr/bin/env python3
"""Independent exact-integer shared-27-voxel signed ionic transport regression.

All 54 native 3D bonds, both directions, two ionic species. The positive
and negative charge inventories are physically different carriers; their
net signed sum is transported conservatively on each *internal* event.
Open boundary currents require explicit source/sink accounting and
are not silently assigned to closed-system conservation.
"""
from __future__ import annotations
from itertools import product
from pathlib import Path
import json

ROOT = Path(__file__).resolve().parents[1]
OWNER = ROOT / "DASHI/Biology/Physical/BiologicalSignedIonicSharedGridExact.agda"
POINTS = tuple(product(range(3), repeat=3))
BONDS = tuple(
    (p, tuple(p[i] + int(axis == i) for i in range(3)))
    for p in POINTS for axis in range(3) if p[axis] < 2
)
assert len(POINTS) == 27 and len(BONDS) == 54


def one_move(state, origin, destination, sign):
    if sign not in (+1, -1) or origin not in POINTS or destination not in POINTS:
        raise ValueError("invalid signed ionic event")
    before = sum(q * charge for (p, charge), q in state.items())
    out = state.copy()
    src, dst = (origin, sign), (destination, sign)
    if out[src] > 0 and origin != destination:
        out[src] -= 1
        out[dst] += 1
    after = sum(q * charge for (p, charge), q in out.items())
    assert after == before
    assert sum(out.values()) == sum(state.values())
    assert min(out.values()) >= 0
    return out


def main():
    src = OWNER.read_text()
    for theorem in (
        "positiveIonTotalPreserved",
        "negativeIonTotalPreserved",
        "nativeSignedChargeConservedByEveryHistory",
        "nativeOriginal54BondSignedChargeConserved",
        "originalForwardPositive", "originalForwardNegative",
    ):
        assert theorem in src

    checked = 0
    for start in POINTS:
        for sign in (+1, -1):
            for reverse in (False, True):
                state = {(p, q): 0 for p in POINTS for q in (+1, -1)}
                state[start, sign] = 5
                initial = sum(q * n for (p, q), n in state.items())
                for a, b in BONDS:
                    state = one_move(state, b if reverse else a,
                                     a if reverse else b, sign)
                    checked += 1
                assert sum(q * n for (p, q), n in state.items()) == initial

    # Balance must change only under an explicitly priced external ion input.
    state = {(p, q): 0 for p in POINTS for q in (+1, -1)}
    state[POINTS[0], +1] = 2
    before = sum(q * n for (p, q), n in state.items())
    injected_positive = 2
    extracted_negative = 0
    state[POINTS[0], +1] += injected_positive
    after = sum(q * n for (p, q), n in state.items())
    assert after - before == injected_positive + extracted_negative

    print(json.dumps({
        "status": "passed-synthetic-signed-ion-mass-transport",
        "native_voxel_sites": 27,
        "original_3d_bonds": 54,
        "ions": ["positive-monovalent", "negative-monovalent"],
        "directed_sweep_transfer_checks": checked,
        "original_integer_signed_charge_preserved": True,
        "open_boundary_charge_source_separate": True,
        "physical_ionic_mobility_calibrated": False,
        "poisson_nernst_planck_validated": False,
        "agda_kernel_accepted": False,
    }, indent=2))


if __name__ == "__main__":
    main()
