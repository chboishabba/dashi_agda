#!/usr/bin/env python3
"""Exhaustively check a FINITE nine-predicate Belnap/Dunn-to-SSP chart.

This is a reference-model regression, not Agda kernel verification.
Original polarity owners: Belnap (1977), Dunn (1976), inherited DASHI
ClaimIndexedEvidencePolarityExact; source and proof ownership retained.
For Woogaroo, negative means a separately asserted ¬P in the same
canonical ground/scope. A zero coarse sign may be both or neither.
No signed synthetic assumption establishes a reviewed record or legal outcome.
"""
from __future__ import annotations
import itertools
import json
from collections import Counter

STATES = ("neither", "positive", "negative", "both")
COARSE = {"neither": 0, "positive": 1, "negative": -1, "both": 0}
GROUNDS = (
    "advice-consideration", "recovery-plan", "incremental-habitat",
    "comment-transmission", "approval-scope", "local-prestart",
    "improper-influence",
)
PREDICATES = (
    "applicable-law", "alleged-defect", "materiality",
    "claimed-compliance", "habitat-concern", "causal-connection",
    "reviewed-original", "same-project-stage", "independent-mediation",
)

def route(defect: str, synthetic_review: bool) -> str:
    if defect == "both":
        return "reconcile-contradiction"
    if synthetic_review and defect == "positive":
        return "applicant-defeater-search"
    if synthetic_review and defect == "negative":
        return "respondent-counter-defeater-search"
    return "acquire-originals"

def verify() -> dict:
    assert len(GROUNDS) == 7 and len(set(GROUNDS)) == 7
    assert len(PREDICATES) == 9 and len(set(PREDICATES)) == 9
    assert COARSE["negative"] == -1 and COARSE["positive"] == 1
    assert COARSE["neither"] == COARSE["both"] == 0
    image = Counter()
    route_counts = Counter()
    fine_count = 0
    for vector in itertools.product(STATES, repeat=9):
        fine_count += 1
        img = tuple(COARSE[x] for x in vector)
        image[img] += 1
        assert len(img) == 9
        for synthetic_review in (False, True):
            label = route(vector[1], synthetic_review)
            route_counts[(synthetic_review, label)] += 1
            assert label != "legal-merits-proved"
            if vector[1] == "both":
                assert label == "reconcile-contradiction"
            if vector[1] == "neither":
                assert label == "acquire-originals"
            if vector[1] == "negative" and synthetic_review:
                assert label == "respondent-counter-defeater-search"

    assert fine_count == 4**9 == 262144
    assert len(image) == 3**9 == 19683
    assert sum(image.values()) == 4**9
    assert max(image.values()) == 2**9
    assert image[(0,) * 9] == 2**9
    assert route_counts[(False, "acquire-originals")] == 3 * 4**8
    for label in (
        "acquire-originals", "applicant-defeater-search",
        "respondent-counter-defeater-search", "reconcile-contradiction",
    ):
        assert route_counts[(True, label)] == 4**8

    # p-adic/CylinderSystem depth is a declared one-branch PREFIX only.
    # Refinement appends one finer digit, so projecting back is exact.
    for lower in itertools.product((-1, 0, 1), repeat=3):
        for finer in (-1, 0, 1):
            assert (lower + (finer,))[:3] == lower

    return {
        "status": "passed",
        "grounds": len(GROUNDS),
        "predicate_slots": len(PREDICATES),
        "fine_evidence_assignments": fine_count,
        "coarse_ternary_codes": len(image),
        "many_to_one_fine_residuals": fine_count - len(image),
        "maximum_coarse_preimages": max(image.values()),
        "synthetic_review_true_count_per_search_role": 4**8,
        "actual_evidence_paid": False,
        "legal_merits_proved": False,
        "triadic_face_glued": False,
        "kernel_checked": False,
        "learned_sophontic_model_tested": False,
    }

if __name__ == "__main__":
    print(json.dumps(verify(), sort_keys=True, indent=2))
