#!/usr/bin/env python3
"""Consistency check of PNAS-reported aggregate, NOT an EEG/fMRI replay.

Original experimental authors: Timmermann et al., PNAS 2023,
DOI 10.1073/pnas.2218949120, main static whole-brain GFC comparison.
"""
import json
from scipy.stats import t as student_t


def audit():
    reported_t = 3.11
    reported_df = 15
    reported_p_rounded = 0.007
    reported_ci_rounded = [0.028, 0.150]
    implied_n = reported_df + 1
    midpoint_of_rounded_ci = sum(reported_ci_rounded) / 2
    reconstructed_se_from_rounded_values = midpoint_of_rounded_ci / reported_t
    p_two_sided = 2 * student_t.sf(reported_t, reported_df)
    ci_half = student_t.ppf(0.975, reported_df) * reconstructed_se_from_rounded_values
    ci_from_rounded_inputs = [midpoint_of_rounded_ci - ci_half,
                              midpoint_of_rounded_ci + ci_half]
    assert implied_n == 16
    assert round(p_two_sided, 3) == reported_p_rounded
    assert all(abs(a - b) < 0.0005 for a, b in zip(ci_from_rounded_inputs,
                                                    reported_ci_rounded))
    return {
        "claim": "Timmermann 2023 main whole-brain GFC DMT-vs-placebo paired contrast",
        "source_doi": "10.1073/pnas.2218949120",
        "reported_t": reported_t, "reported_df": reported_df,
        "implied_n": implied_n, "reported_p_3dp": reported_p_rounded,
        "verified_p_two_sided": float(p_two_sided),
        "reported_ci95": reported_ci_rounded,
        "reconstructed_ci95_from_rounded_values": ci_from_rounded_inputs,
        "status": "published_aggregate_arithmetic_consistent",
        "human_data_recomputed": False, "participant_ids_recovered": False,
        "same_paper_result_reproduced": False,
    }


if __name__ == "__main__":
    print(json.dumps(audit(), sort_keys=True, indent=2))
