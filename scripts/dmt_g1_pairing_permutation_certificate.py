#!/usr/bin/env python3
"""Exact FINITE pairing-information-loss certificate; synthetic data only.

Origin of empirical question: Niedernhuber, Suay, Lenggenhager et al. (2026),
DOI 10.1177/02698811261481062; this code is NOT their analysis or any
experimental reproduction. Earlier Markov statistics: Billingsley, Kullback,
von Wegner et al., Tait and Zhang. Mathematical counterexample / synthetic
adaptation: DASHI (Johl Brown, research direction; OpenAI ChatGPT assistance).

Original source MATLAB jointly drops NaN rows; we DO NOT allege actual author
misalignment. We prove only insufficiency of unkeyed condition marginals.
"""
from __future__ import annotations

import argparse
import json
from fractions import Fraction
from itertools import permutations

DMT = (10, 20, 30)
PLACEBO = (8, 18, 28)


def paired_sample_variance(left, right):
    if len(left) != len(right) or len(left) < 2:
        raise ValueError("At least two paired observations are required")
    differences = tuple(Fraction(a) - Fraction(b) for a, b in zip(left, right))
    center = sum(differences, Fraction(0)) / len(differences)
    return sum(((x - center) ** 2 for x in differences), Fraction(0)) / (len(differences) - 1)


def certificate():
    rows = []
    for perm in permutations(PLACEBO):
        differences = tuple(a - b for a, b in zip(DMT, perm))
        rows.append({
            "placebo_assignment": list(perm),
            "difference_vector": list(differences),
            "mean_difference_exact": str(sum(differences, Fraction(0)) / 3),
            "sample_variance_exact": str(paired_sample_variance(DMT, perm)),
            "cross_moment_exact": str(sum(a * b for a, b in zip(DMT, perm))),
        })
    assert len(rows) == 6
    assert all(r["mean_difference_exact"] == "2" for r in rows)
    aligned = next(r for r in rows if r["placebo_assignment"] == [8, 18, 28])
    reversed_ = next(r for r in rows if r["placebo_assignment"] == [28, 18, 8])
    assert aligned["sample_variance_exact"] == "0"
    assert reversed_["sample_variance_exact"] == "400"
    assert aligned["cross_moment_exact"] == "1280"
    assert reversed_["cross_moment_exact"] == "880"
    return {
        "schema": "dashi-dmt-g1-unkeyed-pairing-exhaustive-v1",
        "scope": "constructed_three_person_pairing_not_original_EEG",
        "input_marginals": {"DMT": list(DMT), "placebo": list(PLACEBO)},
        "assignments": rows,
        "same_marginals_all_worlds": True,
        "same_mean_difference_all_worlds": True,
        "paired_variance_identified_by_unkeyed_marginals": False,
        "original_author_alignment_error_found": False,
        "original_EEG_reproduction": False,
        "external_agent_ontology_established": False,
    }


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("--test", action="store_true")
    opts = p.parse_args()
    result = certificate()
    if opts.test:
        assert {x["sample_variance_exact"] for x in result["assignments"]} == {"0", "100", "300", "400"}
        print("PASS: all six exact finite assignments; source/claim ceilings preserved")
    else:
        print(json.dumps(result, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
