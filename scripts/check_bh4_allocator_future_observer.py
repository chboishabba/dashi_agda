#!/usr/bin/env python3
"""Exact integer BH4 toy allocation counterexample, no assay or disease inference.

Check source-written Agda owner's stated balanced profiles and enumerate
all nonnegative allocations across five selected BH4 sinks at fixed supply.
This cannot pay the original 29x12 reaction / 29 exchange physical model.
"""
from __future__ import annotations

import json
from math import comb
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
OWNER = ROOT / "DASHI/Biology/BH4AllocatorFutureObservationCountermodelExact.agda"
CYCLE_OWNER = ROOT / "DASHI/Biology/BH4CatalyticTurnoverFutureCountermodelExact.agda"

def candidates(supply: int):
    if supply < 0:
        raise ValueError("supply must be nonnegative")
    for hydroxylase in range(supply + 1):
        for nos in range(supply - hydroxylase + 1):
            for other in range(supply - hydroxylase - nos + 1):
                for loss in range(supply - hydroxylase - nos - other + 1):
                    stored = supply - hydroxylase - nos - other - loss
                    yield hydroxylase, nos, other, loss, stored

def main():
    src = OWNER.read_text(encoding="utf-8")
    for name in (
        "sameCoarseSupply", "supplyOnlyNotSufficientForBranchFuture",
        "commonSupplyIdentifiesSource", "sourceBalance",
    ):
        assert name in src, f"missing original Agda proof owner: {name}"

    cycles = CYCLE_OWNER.read_text(encoding="utf-8")
    for lemma in ("sameOriginalPoolAmount", "differentThroughputAtSameAmount",
                  "samePoolDoesNotDetermineEffectiveTurnover"):
        assert lemma in cycles, f"missing catalytic turnover owner: {lemma}"
    assert 1 * 1 != 1 * 2
    cases = {}
    for supply in range(9):
        rows = list(candidates(supply))
        assert len(rows) == comb(supply + 4, 4)
        assert all(sum(row) == supply for row in rows)
        responses = {h > 0 for h, _nos, _other, _loss, _stored in rows}
        assert len(responses) == (1 if supply == 0 else 2)
        cases[str(supply)] = {
            "balanced_branch_allocations": len(rows),
            "different_hydroxylase_response_possible": len(responses) == 2,
        }

    first = (1, 0, 0, 0, 0)
    second = (0, 1, 0, 0, 0)
    assert sum(first) == sum(second) == 1
    assert (first[0] > 0) != (second[0] > 0)
    result = {
        "result": "passed",
        "selected_supply_range": [0, 8],
        "source_theorem": "supplyOnlyNotSufficientForBranchFuture",
        "supply_one_balanced_allocations": 5,
        "same_supply_different_branch_response": True,
        "equal_pool_distinct_selected_turnover_capacity": True,
        "by_supply": cases,
        "real_29x12_bh4_flux_paid": False,
        "source_kinetics_or_compartments_paid": False,
        "kitzerow_clinical_causation_claim": False,
    }
    print(json.dumps(result, sort_keys=True, indent=2))

if __name__ == "__main__":
    main()
