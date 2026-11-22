#!/usr/bin/env python3
"""Exact, synthetic-only algebra for the Wang et al. 2019 alpha-ERD audit.

Original paper: Wang et al., eNeuro 6(2), ENEURO.0483-18.2019,
DOI 10.1523/ENEURO.0483-18.2019.
Original subject EEG and Matlab scripts: CaltechDATA D1.930 / D1.931.

Scientific original authors retain credit for their experiment and data.
This file is an independent DASHI mathematical audit; it does not download,
replay, copy or estimate observed human EEG. No Github CI is required.
"""
import argparse
import csv
import json
from collections import defaultdict
from pathlib import Path
from sympy import Matrix, Rational, symbols

INCLINATION = ("active_sweep", "active_fixed", "sham_sweep", "sham_fixed")
DECLINATION = ("ccw", "cw", "fixed")
LIMITS = {"inclination": 29, "declination": 26}


def contrast_contract():
    baseline, active, sweep, interaction = symbols("baseline active sweep interaction")
    design = Matrix([
        [1, 1, 1, 1],  # active sweep
        [1, 1, 0, 0],  # active fixed
        [1, 0, 1, 0],  # sham sweep
        [1, 0, 0, 0],  # sham fixed
    ])
    interaction_vector = Matrix([[1, -1, -1, 1]])
    # Cancels baseline, active-only, sweep-only and selects interaction.
    assert design.rank() == 4
    assert interaction_vector * design == Matrix([[0, 0, 0, 1]])
    y = design * Matrix([baseline, active, sweep, interaction])
    assert (interaction_vector * y)[0] == interaction
    directions = Matrix([[1, -1, 0], [1, 0, -1]])
    assert directions.rank() == 2
    assert directions * Matrix([1, 1, 1]) == Matrix([0, 0])
    return {"inclination_design_rank": design.rank(),
            "declination_direction_contrast_rank": directions.rank(),
            "symbolic_interaction": str((interaction_vector * y)[0])}


def analyze_rows(rows, mode):
    if mode not in LIMITS:
        raise ValueError("unsupported mode")
    cells = INCLINATION if mode == "inclination" else DECLINATION
    by_id = defaultdict(dict)
    for row in rows:
        pid = row.get("participant_id", "").strip()
        condition = row.get("condition", "").strip()
        if not pid or condition not in cells:
            raise ValueError("missing participant_id or unknown condition")
        if condition in by_id[pid]:
            raise ValueError("duplicate participant+condition; trials must not be treated as people")
        by_id[pid][condition] = Rational(row["alpha_erd_db"].strip())
    if len(by_id) > LIMITS[mode]:
        raise ValueError("participant denominator exceeds source group N")
    complete, missing = {}, {}
    for pid, values in sorted(by_id.items()):
        absent = sorted(set(cells) - set(values))
        if absent:
            missing[pid] = absent
            continue
        if mode == "inclination":
            complete[pid] = {"active_minus_sham_sweep_minus_fixed":
                values["active_sweep"] - values["active_fixed"]
                - values["sham_sweep"] + values["sham_fixed"]}
        else:
            complete[pid] = {
                "ccw_minus_cw": values["ccw"] - values["cw"],
                "ccw_minus_fixed": values["ccw"] - values["fixed"],
            }
    return {"mode": mode, "n_distinct_input_participants": len(by_id),
            "n_complete_matched_participants": len(complete),
            "missing_by_participant": missing,
            "exact_contrasts_by_participant": {k:{n:str(v) for n,v in vals.items()}
                                               for k,vals in complete.items()},
            "WARNING": "Synthetic/externally supplied summarized rows only; NOT original EEG replay or a p-value"}


def synthetic_fixture():
    # Illustrative artificial values, NOT observations from Wang et al.
    raw = [
        ("SYN01", "active_sweep", "-3.5"), ("SYN01", "active_fixed", "-1"),
        ("SYN01", "sham_sweep", "-1.1"), ("SYN01", "sham_fixed", "-1"),
        ("SYN02", "active_sweep", "-4"), ("SYN02", "active_fixed", "-1"),
        ("SYN02", "sham_sweep", "-1"), ("SYN02", "sham_fixed", "-1"),
    ]
    return [{"participant_id": a, "condition": b, "alpha_erd_db": c} for a,b,c in raw]


def self_test():
    contract = contrast_contract()
    demo = analyze_rows(synthetic_fixture(), "inclination")
    assert demo["n_complete_matched_participants"] == 2
    assert demo["exact_contrasts_by_participant"]["SYN01"]["active_minus_sham_sweep_minus_fixed"] == "-12/5"
    assert demo["exact_contrasts_by_participant"]["SYN02"]["active_minus_sham_sweep_minus_fixed"] == "-3"
    incomplete = [r for r in synthetic_fixture() if not (r["participant_id"] == "SYN02" and r["condition"] == "sham_fixed")]
    x = analyze_rows(incomplete, "inclination")
    assert x["n_complete_matched_participants"] == 1
    assert x["missing_by_participant"]["SYN02"] == ["sham_fixed"]
    try:
        analyze_rows(synthetic_fixture() + [synthetic_fixture()[0]], "inclination")
        raise AssertionError("duplicate guard was bypassed")
    except ValueError as e:
        assert "duplicate" in str(e)
    try:
        analyze_rows([{"participant_id": "p" + str(i), "condition": "ccw", "alpha_erd_db": "0"}
                      for i in range(27)], "declination")
        raise AssertionError("denominator guard was bypassed")
    except ValueError as e:
        assert "denominator" in str(e)
    directional = analyze_rows([{"participant_id":"SYN","condition":c,"alpha_erd_db":v}
                                for c,v in zip(DECLINATION, ["-2","-1","0"])], "declination")
    assert directional["exact_contrasts_by_participant"]["SYN"]["ccw_minus_cw"] == "-1"
    assert directional["exact_contrasts_by_participant"]["SYN"]["ccw_minus_fixed"] == "-2"
    return {"status": "PASS", "synthetic_tests": 8, **contract, "illustrative_demo": demo}


def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--csv", type=Path, help="Optional summarized columns: participant_id,condition,alpha_erd_db; NOT raw EEG")
    ap.add_argument("--mode", choices=tuple(LIMITS), default="inclination")
    ns=ap.parse_args()
    if ns.csv:
        contrast_contract()
        with ns.csv.open(newline="", encoding="utf-8") as fh:
            result=analyze_rows(csv.DictReader(fh), ns.mode)
    else:
        result=self_test()
    print(json.dumps(result, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
