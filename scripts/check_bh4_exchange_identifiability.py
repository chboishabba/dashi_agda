#!/usr/bin/env python3
"""Synthetic exact group-cancellation and disambiguation tests; no empirical claims."""
from __future__ import annotations

from copy import deepcopy
from bh4_exchange_identifiability import (
    synthetic_unrestricted_exchange, check_exchange_bounds,
)


def rejects(fn, *args):
    try:
        fn(*args)
    except ValueError:
        return
    raise AssertionError("invalid source coordinate admitted")


def main() -> int:
    matrix = {
        "schema": "dashi.bh4-stoichiometric-matrix.v1",
        "reaction_index": ["RHEA:101", "RHEA:102"],
        "species_index": ["CHEBI:11", "CHEBI:12"],
        "matrix": [[-1, 2], [1, -1]],
    }
    for v in ({"RHEA:101": 0, "RHEA:102": 0},
              {"RHEA:101": 3, "RHEA:102": 5},
              {"RHEA:101": -7, "RHEA:102": 8}):
        x = synthetic_unrestricted_exchange(matrix, v)
        assert x["exact_integer_balance_residual"] == 0
        assert x["usable_for_joint_flux_witness"] is False
        assert x["classification"] == "algebraic-non-identifiability-only"
    x = synthetic_unrestricted_exchange(matrix, {"RHEA:101": 3, "RHEA:102": 5})
    assert x["synthetic_exchange"] == {"CHEBI:11": -7, "CHEBI:12": 2}
    check = check_exchange_bounds(x, {"CHEBI:11": (-10, 10), "CHEBI:12": (-3, 3)})
    assert check["candidate_within_supplied_bounds"] is True
    check = check_exchange_bounds(x, {"CHEBI:11": (-6, 6), "CHEBI:12": (-3, 3)})
    assert check["candidate_within_supplied_bounds"] is False
    assert check["violating_species"] == ["CHEBI:11"]
    assert check["synthetic_candidate_global_feasibility"] is False
    rejects(check_exchange_bounds, x, {"CHEBI:11": (-5, 5)})
    rejects(synthetic_unrestricted_exchange, matrix, {"RHEA:101": 2})
    bad = deepcopy(matrix); bad["matrix"][0][0] = 1.0
    rejects(synthetic_unrestricted_exchange, bad, {"RHEA:101": 3, "RHEA:102": 5})
    print("BH4 exchange cancellation exact-integer non-identifiability regression: ok")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
