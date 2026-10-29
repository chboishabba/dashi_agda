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

def route(vector: tuple[str, ...], synthetic_review: bool) -> str:
    if "both" in vector:
        return "reconcile-contradiction"
    common = (synthetic_review
              and vector[0] == "positive"
              and vector[6] == "positive"
              and vector[7] == "positive")
    if not common:
        return "acquire-originals"
    if vector[1] == "positive" and vector[2] == "positive" and vector[3] != "positive":
        return "applicant-defeater-search"
    if vector[1] == "negative" and vector[3] == "positive":
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
            label = route(vector, synthetic_review)
            route_counts[(synthetic_review, label)] += 1
            assert label != "legal-merits-proved"
            if "both" in vector:
                assert label == "reconcile-contradiction"
            if vector[1] == "neither":
                assert label == "acquire-originals"
            if not synthetic_review and "both" not in vector:
                assert label == "acquire-originals"

    assert fine_count == 4**9 == 262144
    assert len(image) == 3**9 == 19683
    assert sum(image.values()) == 4**9
    assert max(image.values()) == 2**9
    assert image[(0,) * 9] == 2**9
    assert route_counts[(False, "acquire-originals")] == 3**9
    assert route_counts[(False, "reconcile-contradiction")] == 4**9 - 3**9
    assert route_counts[(True, "applicant-defeater-search")] == 54
    assert route_counts[(True, "respondent-counter-defeater-search")] == 81
    assert route_counts[(True, "acquire-originals")] == 19548
    assert route_counts[(True, "reconcile-contradiction")] == 4**9 - 3**9
    assert route(("neither",)*9, True) == "acquire-originals"
    assert route(("neither","negative") + ("neither",)*7, True) == "acquire-originals"

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
        "synthetic_review_true_routes": {
            name: route_counts[(True, name)] for name in (
                "acquire-originals", "applicant-defeater-search",
                "respondent-counter-defeater-search", "reconcile-contradiction")
        },
        "actual_evidence_paid": False,
        "legal_merits_proved": False,
        "triadic_face_glued": False,
        "kernel_checked": False,
        "learned_sophontic_model_tested": False,
    }

if __name__ == "__main__":
    print(json.dumps(verify(), sort_keys=True, indent=2))
