#!/usr/bin/env python3
"""Finite reference audit for EPBC 2019/8575 source-typed offset SAT data.

Sources: PD v5 A16 Table 44 (Saunders Havill, Mount Walker West);
PD v5 A15 Table 33 (One Environment, Avonvale), 2025 survey.
No random-sampling assumption, ecological calculator rerun, accepted species
detection, legal merits, actual site breach or independent field validation.
"""
from __future__ import annotations
import argparse
import itertools
import json
from pathlib import Path

MWW_TREES = (0, 2, 0, 1, 0)
AVON_TREES = (11, 5, 0, 0, 1)
TREES_PER_SAT = 30
MWW_REPORTED_PRESENCE = (10, 10, 10, 10)
MWW_TABLE44 = ("T1", "T2", "T3", "T7", "T8")
MWW_OTHER_PROSE = ("T1", "T6", "T7", "T8", "T10")
AVON_TABLE33 = ("T1", "T6", "T7", "T8", "T10")
MWW_REPORTED_OFFSET_BASIS_POINTS = {
    "koala": 5002, "grey_headed_flying_fox": 6689,
    "swift_parrot": 9192, "regent_honeyeater": 3740,
}

def finite_checks() -> dict:
    assert len(MWW_TREES) == len(AVON_TREES) == 5
    assert all(0 <= n <= TREES_PER_SAT for n in (*MWW_TREES, *AVON_TREES))
    assert sum(MWW_TREES) == 3
    assert sum(AVON_TREES) == 17
    assert sum(n > 0 for n in MWW_TREES) == 2
    assert sum(n > 0 for n in AVON_TREES) == 3
    assert len(MWW_REPORTED_PRESENCE) == 4
    assert all(n == 10 for n in MWW_REPORTED_PRESENCE)
    assert sum(MWW_REPORTED_PRESENCE) == 40
    assert MWW_TABLE44 != MWW_OTHER_PROSE
    assert MWW_OTHER_PROSE == AVON_TABLE33

    # If only site positivity and no AU join are supplied, every AU can
    # independently be used or not, subject to at least one used AU.
    # These are hypothetical latent worlds, NOT actual animal locations.
    worlds = list(itertools.product((False, True), repeat=4))
    site_positive = [w for w in worlds if any(w)]
    assert len(worlds) == 16 and len(site_positive) == 15
    for i in range(4):
        assert any(w[i] for w in site_positive)
        assert any(not w[i] for w in site_positive)

    # RAW presence subscores only, NOT weighted MHQA/OAG outcomes.
    raw_totals = [sum(v) for v in itertools.product(range(11), repeat=4)]
    assert len(raw_totals) == 11**4 == 14641
    assert min(raw_totals) == 0 and max(raw_totals) == 40
    assert set(raw_totals) == set(range(41))
    assert all(0 <= n <= 10000 for n in MWW_REPORTED_OFFSET_BASIS_POINTS.values())

    return {
        "case": "EPBC 2019/8575",
        "decision_date": "2026-10-16",
        "evidence_stage": "proponent_reported_not_independently_site_verified",
        "mount_walker_west": {
            "positive_scat_trees_per_30_tree_SAT": MWW_TREES,
            "positive_trees_total": sum(MWW_TREES),
            "positive_SATs": sum(n > 0 for n in MWW_TREES),
            "surveyed_tree_slots": 150,
            "reported_four_AU_presence_scores": MWW_REPORTED_PRESENCE,
            "reported_raw_score_sum_not_weighted": 40,
            "transect_label_discrepancy": MWW_TABLE44 != MWW_OTHER_PROSE,
            "table44_labels": MWW_TABLE44,
            "separate_prose_labels": MWW_OTHER_PROSE,
        },
        "avonvale": {
            "positive_scat_trees_per_30_tree_SAT": AVON_TREES,
            "positive_trees_total": sum(AVON_TREES),
            "positive_SATs": sum(n > 0 for n in AVON_TREES),
            "surveyed_tree_slots": 150,
        },
        "esk": {"survey_table": "not_yet_extracted", "reported_scat_evidence": True},
        "adversarial": {
            "unlocated_AU_use_worlds": len(worlds),
            "site_positive_worlds_without_AU_join": len(site_positive),
            "AU_use_identified_from_exposed_data": False,
            "raw_presence_subscore_allocations": len(raw_totals),
            "raw_score_range_not_ecological_CI": [min(raw_totals), max(raw_totals)],
            "OAG_percentage_recomputed": False,
        },
        "proponent_reported_MWW_offset_percent": {
            k: v/100 for k,v in MWW_REPORTED_OFFSET_BASIS_POINTS.items()
        },
        "limits": [
            "tree slots are not koalas or independent random draws",
            "zero scat at a transect does not prove absence in an AU",
            "no SAT-to-AU coordinate join has been admitted",
            "the 10/10 rubric may permit site-level on-or-adjacent evidence",
            "no approved final OAMP version/calculator re-run",
            "no independent ecological equivalence, breach or judicial finding",
        ],
        "agda_kernel_verified": False,
    }

def check_agda_contract(source: str) -> None:
    for token in (
        "mountWalkerThreePositiveTrees", "avonvaleSeventeenPositiveTrees",
        "mountWalkerTwoPositiveSATs", "avonvaleThreePositiveSATs",
        "allFourPresenceComponentsTotal", "noUniversalAU1UseDecoder",
        "habitatGroundCountermodel", "CompleteOffsetDischarge",
        "originalAUSurveyCoordinates", "final20261015OffsetPlanVersionIdentity",
    ):
        assert token in source, token
    for disallowed in ("postulate ", "{!!}", "allow-unsolved-metas", "TERMINATING"):
        assert disallowed not in source, disallowed

def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--agda-file", type=Path)
    parser.add_argument("--out", type=Path)
    args = parser.parse_args()
    result = finite_checks()
    if args.agda_file is not None:
        check_agda_contract(args.agda_file.read_text())
    result["agda_source_contract_checked"] = args.agda_file is not None
    payload = json.dumps(result, indent=2, sort_keys=True) + "\n"
    if args.out is not None:
        args.out.write_text(payload)
    print(payload, end="")

if __name__ == "__main__":
    main()
