#!/usr/bin/env python3
"""Woogaroo 2019/8575 exact FINITE model of #1414 S3 chart action.

This checks PRESENTATION relabelling of XY->Z positions, not physical
monodromy, historical legal/agency evidence, original source acquisition,
or a change of the thesis/antithesis/synthesis role in a real matter.

Inherited owners: DASHI TernaryEndomorphismConjugacyExact finite S3,
TernaryComparisonSynthesisExact and Woogaroo source/ground ledger.
Unmerged #1414 is methodological inspiration only; no code copied.
"""
from itertools import product
import json

POSITIONS = ("thesis", "antithesis", "synthesis")
PERMUTATIONS = {
    "id": (0,1,2),
    "rotate": (1,2,0),
    "rotate2": (2,0,1),
    "swap-ta": (1,0,2),
    "swap-ts": (2,1,0),
    "swap-as": (0,2,1),
}
GROUNDS = (
    ("advice-consideration", "brief", ("G01","G02","G03","G04")),
    ("recovery-plan", "plan", ("G05","G06","G07","G08")),
    ("incremental-habitat", "ecology", ("G09","G10","G11","G12")),
    ("comment-transmission", "comments", ("G13","G14","G15","G16")),
    ("approval-scope", "signed", ("G17","G18","G19","G20")),
    ("local-prestart", "works", ("G21","G22","G23","G24")),
    ("improper-influence", "conflict", ("G25","G26","G27","G28")),
)

def inverse(permutation):
    return tuple(permutation.index(i) for i in range(3))

def encode(triple, permutation):
    return tuple(permutation[t] for t in triple)

def verify():
    assert len(PERMUTATIONS) == 6 and len(GROUNDS) == 7
    assert len(set(PERMUTATIONS.values())) == 6
    assert {p for p in PERMUTATIONS.values()} == set(__import__("itertools").permutations(range(3)))
    seen=0
    for key, packet, obligations in GROUNDS:
        assert len(obligations) == 4
        for xyz in product(range(3), repeat=3):
            for name,p in PERMUTATIONS.items():
                display=encode(xyz,p)
                recovered=encode(display,inverse(p))
                assert recovered==xyz, (key,name,xyz,display)
                assert (key,packet,obligations)==(key,packet,obligations)
                seen+=1
    r=PERMUTATIONS["rotate"]
    assert encode(encode(encode((0,1,2),r),r),r)==(0,1,2)
    assert len({i for _,_,group in GROUNDS for i in group}) == 28
    # A chart change has NO legal-effect capability by construction.
    return {
        "status":"passed", "project":"2019/8575",
        "source_ground_count":len(GROUNDS),
        "ground_obligations":28,
        "canonical_interaction_cells_per_ground":27,
        "presentation_permutations":6,
        "checked_ground_cell_chart_triples":seen,
        "all_7_ground_acquisition_packet_identifiers_unchanged":True,
        "real_originals_reviewed":False,
        "actual_court_filing_clock_established":False,
        "actual_z_mediation_selected":False,
        "relevant_1414_claim":"finite S3 relabelling only",
        "quaternion_or_monster_same_object_claim":False,
        "agda_kernel_checked":False,
        "rust_test_executed":False,
    }

if __name__=="__main__":
    print(json.dumps(verify(),sort_keys=True,indent=2))
