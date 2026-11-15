#!/usr/bin/env python3
"""Consume an existing NS held-out falsification and select a live next experiment.

Evidence source is the archived matched N32/N48/N64 baseline, not recomputed
or invented measurements. Selection is consumer-specific and never closes Clay.
"""
import argparse
import hashlib
import json
from pathlib import Path

NEGATIVE_MARGINS = {"0.01": -0.01, "0.05": -0.05, "0.10": -0.10, "0.25": -0.25}
SOURCE = "docs/ns_exact_galerkin_coherence_baseline_results.md"
CANDIDATES = (
    {"key": "repeat_self_advection", "cost": 1, "target": "already_falsified_self_advection"},
    {"key": "cross_shell_coherence", "cost": 2, "target": "cross_shell_depletion"},
    {"key": "vorticity_turnover", "cost": 3, "target": "direction_turnover"},
    {"key": "projector_gap", "cost": 4, "target": "spectral_gap"},
)


def choose(margins=NEGATIVE_MARGINS):
    if not margins or not all(float(v) < 0 for v in margins.values()):
        raise ValueError("no verified nonvacuous negative margins")
    live = {"cross_shell_depletion", "direction_turnover", "spectral_gap"}
    scored = [
        {**move, "admissible": move["target"] in live, "current_residual": "B7 Q4/E or Q5 physical control"}
        for move in CANDIDATES
    ]
    permitted = [x for x in scored if x["admissible"]]
    selected = min(permitted, key=lambda x: x["cost"])
    result = {
        "schema": "dashi.verid.ns_abcd_bidi_falsification_replay.v1",
        "source": SOURCE,
        "evidence_kind": "published_repository_report_not_reexecuted",
        "matched_cutoffs": [32, 48, 64],
        "holdout_cutoff": 64,
        "nonvacuous_heldout_margins": margins,
        "observed_status": "self_advective_depletion_candidate_falsified_on_declared_fixture",
        "canonical_leaf": "b7IntegratedControl",
        "selection_rule": "least declared cost among admissible moves addressing live residual",
        "candidate_portfolio": scored,
        "selected_next_experiment": selected["key"],
        "selection_kind": "proposed_numerical_probe_not_physical_authorization",
        "unpaid": [
            "run selected next numerical experiment and compare actual predicted observable",
            "derive real physical Q4/E control or Q5 fallback",
            "calibrate numerical/formal and numerical/physical gaps",
        ],
        "promotion": {"formal_NS_B7": False, "continuum": False, "clay": False},
    }
    result["digest"] = hashlib.sha256(json.dumps(result,sort_keys=True,separators=(",",":")).encode()).hexdigest()
    return result


def main():
    p=argparse.ArgumentParser()
    p.add_argument("--output-json",type=Path,required=True)
    a=p.parse_args()
    report=choose()
    a.output_json.parent.mkdir(parents=True,exist_ok=True)
    a.output_json.write_text(json.dumps(report,sort_keys=True,indent=2)+"\n")
    print(report["selected_next_experiment"],report["digest"])


if __name__=="__main__":
    main()
