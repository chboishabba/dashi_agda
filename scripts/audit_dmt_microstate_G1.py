#!/usr/bin/env python3
"""Source-attributed +microstate G1 rational-count reconstruction (synthetic ONLY).

Original code: L. Tait & J. Zhang, +microstate toolbox, NeuroImage (2022),
DOI 10.1016/j.neuroimage.2022.119346, commit
1ce32466bbd49b9751bbe8575a8b7422ff2540fe,
+microstate/@individual/stats_markov.m, blob
a738a95c4218b8de76920e8333cef307126ef13f.

Applied by Niedernhuber et al. (2026), DOI 10.1177/02698811261481062,
original DMT_microstates commit c5c064d109563e97127403a8fbb340009ba1e88b,
disemb_mc_Rprep.m: coh.stats(idx).markov.G1.

The source also cites von Wegner et al. for Markov/syntax statistics.
Local implementation is an independent compatibility translation of count
arithmetic, NOT MATLAB execution, fitted maps, EEG replay or novel theory.
"""
from __future__ import annotations

import argparse
import json
import math
from collections import Counter
from pathlib import Path

SCHEMA = "dashi-dmt-microstate-g1-synthetic-v1"
ORIGINAL_TOOLBOX_BLOB = "a738a95c4218b8de76920e8333cef307126ef13f"


def g1_counts(labels):
    """Count consecutive triples with precisely the source's time indices.

    Input is ONE contiguous stream. Never silently glue trial/condition epochs.
    MATLAB's zero-count eps convention changes values only by negligible
    floating contributions; nonzero support has the exact same count ratio.
    """
    if not isinstance(labels, list) or len(labels) < 3 or any(
            type(x) is not int or x < 1 for x in labels):
        raise ValueError("Need >=3 ordered positive integer microstate labels")
    active = sorted(set(labels))
    # Source MATLAB stats_markov.m removes unobserved state indices before
    # computing f_ijk. Preserve that behavior for gapped 1-based labels;
    # report the original support to avoid pretending a source state existed.
    dense_map = {label: i + 1 for i, label in enumerate(active)}
    dense = [dense_map[label] for label in labels]
    k = len(active)
    triple = Counter(zip(dense[:-2], dense[1:-1], dense[2:]))
    center = Counter(dense[1:-1])
    forward = Counter(zip(dense[1:-1], dense[2:]))
    backward = Counter(zip(dense[:-2], dense[1:-1]))
    terms = []
    for (prev, mid, following), n in triple.items():
        numerator = n * center[mid]
        denominator = forward[mid, following] * backward[prev, mid]
        if denominator <= 0:
            raise ArithmeticError("Impossible positive triple with missing margin")
        terms.append(n * math.log(numerator / denominator))
    g1 = 2.0 * math.fsum(terms)
    # Floating cancellation can yield tiny negative values from an exact
    # nonnegative conditional-information statistic.
    if -1e-10 < g1 < 0:
        g1 = 0.0
    return {"g1": g1, "k_observed": k, "original_state_support": active,
            "unobserved_state_indices_compacted": active != list(range(1, max(active) + 1)),
            "triples": len(labels) - 2,
            "df_original_chi_square": k * (k - 1) ** 2,
            "nonzero_triple_cells": len(triple),
            "no_boundary_transition_inferred": True,
            "statistic_is_2n_conditional_mutual_information_nats": True}


def synthetic_evaluate(document):
    if not isinstance(document, dict) or set(document) != {
            "schema", "mode", "source_id", "labels", "single_contiguous_stream"}:
        raise ValueError("Strict synthetic label-only source schema")
    if document["schema"] != SCHEMA or document["mode"] != "synthetic":
        raise ValueError("Cannot admit real EEG labels or inferred trial data")
    if not isinstance(document["source_id"], str) or not document["source_id"].startswith("synthetic:"):
        raise ValueError("Synthetic source namespace required")
    if document["single_contiguous_stream"] is not True:
        raise ValueError("Unknown epoch boundaries can change G1")
    result = g1_counts(document["labels"])
    result.update({
        "schema": "dashi-dmt-microstate-g1-synthetic-result-v1",
        "original_algorithm": "plus-microstate @individual/stats_markov.m G1",
        "original_toolbox_git_blob": ORIGINAL_TOOLBOX_BLOB,
        "synthetic_only": True,
        "actual_eeg_participant_data_replayed": False,
        "original_p_value_reproduced": False,
        "independent_external_agents_inferred": False,
    })
    return result


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("synthetic_label_json", type=Path)
    a = p.parse_args()
    print(json.dumps(synthetic_evaluate(json.loads(
        a.synthetic_label_json.read_text(encoding="utf8"))), indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
