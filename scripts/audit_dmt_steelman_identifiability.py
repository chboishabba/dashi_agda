#!/usr/bin/env python3
"""Exact rational DMT latent-model adversary: finite observational equivalence.

A deliberately synthetic witness, not an active-inference implementation, nor
an fMRI or phenomenology fit. Two hidden-state interpretations with identical
stochastic kernels and emission laws have identical observed likelihoods for
every finite word. This is enough to defeat *semantic* inference to external
agency from a generic fixed-Q HMM/trace law.

Original mathematical fact: latent-state label invariance of Markov/HMM
observations. This script is a DASHI domain-specific audit of that fact.
Original DMT sources and model donors are cited in the companion ledger.
"""
from __future__ import annotations

import argparse
import itertools
import json
from fractions import Fraction as F

INITIAL = (F(2, 5), F(3, 5))
Q = ((F(3, 4), F(1, 4)), (F(1, 3), F(2, 3)))
P_PRESENCE = (F(1, 5), F(4, 5))
LABELS = {
    "M1_endogenous": ("endogenous_low_agency_attribution",
                       "endogenous_high_agency_attribution"),
    "M2_agent_story": ("latent_agent_state_alpha", "latent_agent_state_beta"),
}


def _valid_probability_row(row):
    return bool(row) and all(isinstance(x, F) and 0 <= x <= 1 for x in row) and sum(row) == 1


def check():
    if not _valid_probability_row(INITIAL) or not all(
        _valid_probability_row(row) for row in Q
    ):
        raise ValueError("Missing normalized exact Markov probabilities")
    if any(not isinstance(x, F) or not 0 <= x <= 1 for x in P_PRESENCE):
        raise ValueError("Invalid emission probabilities")
    if len(INITIAL) != len(Q) or len(P_PRESENCE) != len(Q):
        raise ValueError("Hidden-state dimensions disagree")


def probability(word, *, state_meaning):
    """Forward algorithm, exactly rational, same measured binary alphabet."""
    check()
    if state_meaning not in LABELS:
        raise ValueError("Unknown causal story")
    if any(bit not in (0, 1) for bit in word):
        raise ValueError("Only observed 0/1 presence reports admissible")
    if not word:
        return F(1)
    alpha = [INITIAL[s] * (
        P_PRESENCE[s] if word[0] else (1 - P_PRESENCE[s])
    ) for s in range(2)]
    for bit in word[1:]:
        alpha = [
            sum(alpha[prior] * Q[prior][nxt] for prior in range(2))
            * (P_PRESENCE[nxt] if bit else (1 - P_PRESENCE[nxt]))
            for nxt in range(2)
        ]
    return sum(alpha)


def enumerate_observational_equivalence(max_length=6):
    if not isinstance(max_length, int) or not 1 <= max_length <= 10:
        raise ValueError("Bounded exact witness requires horizon 1..10")
    for length in range(1, max_length + 1):
        words = tuple(itertools.product((0, 1), repeat=length))
        mass_m1 = sum(probability(x, state_meaning="M1_endogenous") for x in words)
        mass_m2 = sum(probability(x, state_meaning="M2_agent_story") for x in words)
        if mass_m1 != mass_m2 or mass_m1 != 1:
            raise AssertionError("Finite observation law not normalized")
        for w in words:
            if probability(w, state_meaning="M1_endogenous") != probability(
                w, state_meaning="M2_agent_story"
            ):
                raise AssertionError("Observed word separated relabelled HMMs")
    return {
        "status": "synthetic_finite_word_equivalence",
        "checked_horizons": list(range(1, max_length + 1)),
        "checked_binary_words": 2 ** (max_length + 1) - 2,
        "all_word_probabilities_equal": True,
        "finite_total_probability_each_horizon": "1",
        "models_share_observation_distribution": True,
        "inference_to_external_entity_permitted": False,
        "any_finite_observation_word_separates_these_models": False,
        "unbounded_theoretical_reason": "The two generators differ only in latent interpretation labels, not INITIAL/Q/emissions. Thus the forward recursion is identical for every finite observed word.",
        "claim_scope": "An *unrestricted* endogenous two-state HMM can exactly implement this M2-style fixed-Q observable law. This does not show every mechanistically restricted M1 matches every M2, nor refute unobserved external agents.",
    }


def hidden_target_accuracy():
    """Independent, fair, sealed binary target vs observed binary report.

    Any deterministic predictor g(O) has P[g(O)=Z]=1/2 if Z independent
    and fair. A leaked observation O'= (O,Z) has trivial accuracy 1.
    This is a design sanity check, not a human information-transfer result.
    """
    exposed = list(itertools.product((0, 1), repeat=2))
    independent_scores = {}
    for b0, b1 in exposed:
        score = sum(
            F(1, 4) * (1 if (b0 if o == 0 else b1) == target else 0)
            for o, target in exposed
        )
        independent_scores[f"{b0}{b1}"] = str(score)
    return {
        "all_observation_only_predictors_accuracy": independent_scores,
        "best_unleaked_target_accuracy": "1/2",
        "leaked_target_accuracy": "1",
        "measurement_scope": "pure synthetic independent fair target",
        "source_dmt_study_had_concealed_target": False,
    }


def audit(max_length=6):
    return {
        "models": LABELS,
        "source_of_mathematical_fact": "finite-state hidden Markov observation equivalence; conventional stochastic theory",
        "model_status": "synthetic semantic-relabelling witness, not Mago active-inference mechanism and not an empirical Hoffman model",
        "observational_equivalence": enumerate_observational_equivalence(max_length),
        "hidden_target": hidden_target_accuracy(),
        "research_discriminator": "Requires an independently specified mechanistic restriction or genuinely new measured/intervened consumer; phenomenological presence reports and generic fixed-Q trace identities alone cannot discriminate.",
    }


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("--max-length", type=int, default=6)
    p.add_argument("--output")
    a = p.parse_args()
    result = json.dumps(audit(a.max_length), indent=2, sort_keys=True) + "\n"
    if a.output:
        from pathlib import Path
        Path(a.output).write_text(result, encoding="utf8")
    else:
        print(result)


if __name__ == "__main__":
    main()
