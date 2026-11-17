#!/usr/bin/env python3
"""Published-aggregate and synthetic-identification audit for Erowid motifs.

Original empirical source: Noah, Shen, Earth Erowid, Fire Erowid, Silver
(2024), DOI 10.3389/fpsyg.2024.1397064. Counts are reported by AUTHORS;
none are computed from raw Erowid narratives (no report access licensed here).

Mathematics: distinct stochastic transitions can preserve IDENTICAL static
marginals. The example uses arbitrary UNIFORM THREE-STATE TOY marginals,
not estimated Erowid category proportions or subject timelines.

No corpus scraping, API calls, NLP classification, or ontology inference.
"""
from __future__ import annotations
from fractions import Fraction as F
import itertools
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
BRIDGE = ROOT / "Docs/receipts/DMTRecurringMotifErowidPriorArtBridge20261025.json"
STATES = ("lattice", "tunnel", "face")
INITIAL = (F(1, 3),) * 3
KERNELS = {
    "absorbing_identity": ((F(1), F(0), F(0)),
                           (F(0), F(1), F(0)),
                           (F(0), F(0), F(1))),
    "deterministic_three_cycle": ((F(0), F(1), F(0)),
                                  (F(0), F(0), F(1)),
                                  (F(1), F(0), F(0))),
    "uniform_iid_mixing": ((F(1, 3),) * 3,) * 3,
}
SOURCE_DOI = "10.3389/fpsyg.2024.1397064"


def validate_stochastic(kernel):
    if len(kernel) != 3 or any(
        len(row) != 3 or any(v < 0 or v > 1 for v in row) or sum(row) != 1
        for row in kernel
    ):
        raise ValueError("Invalid exact three-state stochastic matrix")


def projected_distribution(p, kernel):
    validate_stochastic(kernel)
    return tuple(sum(p[i] * kernel[i][j] for i in range(3))
                 for j in range(3))


def stationary_marginal_counterexample():
    for kernel in KERNELS.values():
        assert projected_distribution(INITIAL, kernel) == INITIAL
    cycle = KERNELS["deterministic_three_cycle"]
    identity = KERNELS["absorbing_identity"]
    iid = KERNELS["uniform_iid_mixing"]
    # A pair measurement WOULD separate them. The source article's static
    # substance-indexed category frequencies are not such pair measurements.
    joint = {
        name: tuple(tuple(INITIAL[i] * k[i][j] for j in range(3))
                    for i in range(3)) for name, k in KERNELS.items()
    }
    assert joint["deterministic_three_cycle"] != joint["absorbing_identity"]
    assert joint["uniform_iid_mixing"] != joint["deterministic_three_cycle"]
    assert cycle[0][1] == 1 and identity[0][1] == 0 and iid[0][1] == F(1, 3)
    return {
        "status": "exact_synthetic_nonidentification",
        "states": list(STATES),
        "toy_stationary_marginals": [str(x) for x in INITIAL],
        "distinct_kernels": list(KERNELS),
        "all_kernels_same_one_time_marginals": True,
        "observed_transition_joint_distributions_are_different": True,
        "lattice_to_tunnel_probabilities": {
            k: str(v[0][1]) for k, v in KERNELS.items()
        },
        "transition_kernel_estimated_from_erowid": False,
        "three_cycle_is_original_repository_toy_not_empirical_measurement": True,
        "logical_conclusion": "Cross-report one-time motif prevalence cannot determine within-experience transition or recurrence. Stationary marginals do not identify a stochastic generator.",
        "does_not_refute_endogenous_or_agent_ontology": True,
    }


def published_counts(bridge=None):
    if bridge is None:
        bridge = json.loads(BRIDGE.read_text(encoding="utf-8"))
    src = bridge["original_published_research"]
    if src["doi"] != SOURCE_DOI:
        raise ValueError("Original source DOI differs")
    q = src["reported_dataset"]
    if (q["reports"] != 39586 or q["dmt_reports"] != 1121
            or q["sentences"] != 2246254
            or q["visual_effect_sentences"] != 143520):
        raise ValueError("Paper numbers changed: separately source-check revision")
    if "Entities" not in src["published_categories"]:
        raise ValueError("Original Entities category missing")
    ratio = F(q["visual_effect_sentences"], q["sentences"])
    # Both values appear in different parts of the original publication.
    # 2,246,254 was labelled the Pearson chi-square N; its equivalence to
    # denominator used for the published 6.52% is not documented here.
    return {
        "status": "published_aggregate_arithmetic_only",
        "source_doi": SOURCE_DOI,
        "report_count": q["reports"], "DMT_report_count": q["dmt_reports"],
        "visual_effect_sentences": q["visual_effect_sentences"],
        "reported_chi_square_N": q["sentences"],
        "source_stated_visual_fraction_percent": str(q["visual_effect_fraction_rounded"] * 100),
        "calculated_percent_if_chi_square_N_is_denominator": round(float(ratio * 100), 6),
        "counts_not_arithmetically_equal_to_published_percent": abs(
            float(ratio * 100) - q["visual_effect_fraction_rounded"] * 100
        ) > 0.005,
        "cross_denominator_reconciliation_found": False,
        "raw_report_data_accessed": False,
        "subject_or_report_level_entity_prevalence_computed": False,
        "measured_motif_transition_matrix_computed": False,
        "independent_replication_of_original_narrative_classifier": False,
        "claim_scope": "Source-reported 6.52% and 143,520 visual sentences are both retained; 2,246,254 was reported as chi-square N. Cross-denominator meaning is unresolved, not arbitrarily repaired.",
    }


def audit():
    return {
        "source": published_counts(),
        "mathematical_adversary": stationary_marginal_counterexample(),
        "paper_category_is_not_a_verified_external_entity": True,
        "source_author_roles": "Sean Noah; Miranda Shen; Earth Erowid; Fire Erowid; Michael Silver",
        "model_discriminator": "Recover rights-permitted report-level or prospective within-experience timing with participant/report clustering, then compare mechanistic M1a, M1b and restricted M2 on the same observations; published counts alone cannot decide their transition laws.",
    }


if __name__ == "__main__":
    print(json.dumps(audit(), indent=2, sort_keys=True))
