#!/usr/bin/env python3
"""Exact finite XOR-grid dynamic check, not an IIT/PyPhi or Agda-kernel check.

Imports the repo-owned update rule from iit_xor_grid_calibration, instead of
implementing a second and potentially divergent XOR grid. Exhaustively
tests every 4-bit state. Original Aaronson/Tononi positions are NOT
claims established or refuted by this tiny fixture.
"""
from __future__ import annotations

from collections import Counter
from itertools import product
import hashlib
import json
from iit_xor_grid_calibration import grid2x2_step

STATES = tuple(product((0, 1), repeat=4))
ZERO = (0, 0, 0, 0)
EDGES = (
    ("NE", "NW"), ("SW", "NW"), ("NW", "NE"), ("SE", "NE"),
    ("NW", "SW"), ("SE", "SW"), ("NE", "SE"), ("SW", "SE"),
)


def audit() -> dict:
    table = tuple((s, grid2x2_step(s), grid2x2_step(grid2x2_step(s)))
                  for s in STATES)
    fiber = Counter(out for _, out, _ in table)
    first_outputs = sorted(fiber)
    expected = sorted((p, q, q, p) for p, q in product((0, 1), repeat=2))
    assert first_outputs == expected, (first_outputs, expected)
    assert len(first_outputs) == 4
    assert set(fiber.values()) == {4}, fiber
    assert all(last == ZERO for _, _, last in table)
    assert grid2x2_step(ZERO) == ZERO
    assert ("NW", "NE") in EDGES and ("NE", "NW") in EDGES
    assert grid2x2_step((1, 0, 0, 0)) != ZERO  # nilpotence index is 2
    assert sum(x == ZERO for _, x, _ in table) == 4
    payload = [{"input": list(s), "after_one": list(o), "after_two": list(t)}
               for s, o, t in table]
    canonical = json.dumps(payload, sort_keys=True, separators=(",", ":")).encode()
    return {
        "kind": "source_same_step_finite_enumeration_not_phi_or_phenomenology",
        "source_owner": "DASHI/Biology/IITXORGridAdversarialExact.agda",
        "python_step_owner": "scripts/iit_xor_grid_calibration.py",
        "state_count": len(STATES),
        "distinct_one_step_outputs": len(first_outputs),
        "each_one_step_image_fiber_size": 4,
        "all_states_zero_by_second_step": True,
        "already_zero_after_first_step_count": 4,
        "source_graph_has_directed_two_edge_cycle": True,
        "transition_has_nonzero_fixed_or_periodic_orbit": False,
        "first_step_image": [list(x) for x in first_outputs],
        "table_sha256": hashlib.sha256(canonical).hexdigest(),
        "interpretation": (
            "feedback in declared dependency topology does not imply "
            "sustained nonzero dynamics, empirical memory, IIT phi, or awareness"
        ),
    }


if __name__ == "__main__":
    print(json.dumps(audit(), sort_keys=True, indent=2))
