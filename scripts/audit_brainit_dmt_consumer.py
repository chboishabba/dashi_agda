#!/usr/bin/env python3
"""Exact four-world consumer audit; NOT Brain-IT or DMT measurements."""
from fractions import Fraction as F
from itertools import product
import json


def audit():
    # Independent viewed image S and independently concealed target Z.
    worlds = [(s, z) for s, z in product((0, 1), repeat=2)]
    mass = F(1, len(worlds))
    seen = lambda w: w[0]  # deliberately PERFECT stimulus observation
    reconstructed = lambda b: b
    stimulus_accuracy = sum(
        (mass for w in worlds if reconstructed(seen(w)) == w[0]), F(0))
    assert stimulus_accuracy == 1

    # Every deterministic function of S alone remains at chance on Z.
    decoder_scores = {}
    for guess0, guess1 in product((0, 1), repeat=2):
        guess = (guess0, guess1)
        accuracy = sum(
            (mass for w in worlds if guess[seen(w)] == w[1]), F(0))
        decoder_scores[f"{guess0}{guess1}"] = str(accuracy)
        assert accuracy == F(1, 2)

    # Exact finite independence, without float rounding or an invented MI.
    for s, z in worlds:
        joint = sum((mass for w in worlds if w == (s, z)), F(0))
        marginal_s = sum((mass for w in worlds if w[0] == s), F(0))
        marginal_z = sum((mass for w in worlds if w[1] == z), F(0))
        assert joint == marginal_s * marginal_z == F(1, 4)

    # Ordinary leakage is a stronger competitor than unusual ontology.
    leaked_seen = lambda w: (w[0], w[1])
    leaked_decode = lambda b: b[1]
    leaked_accuracy = sum(
        (mass for w in worlds if leaked_decode(leaked_seen(w)) == w[1]), F(0))
    assert leaked_accuracy == 1

    return {
        "status": "exact_synthetic_consumer_separation_passed",
        "sample_origin": "invented four-world fixture; NOT human neural/DMT data",
        "world_count": len(worlds),
        "perfect_viewed_stimulus_reconstruction": str(stimulus_accuracy),
        "all_stimulus_only_secret_decoder_scores": decoder_scores,
        "secret_given_stimulus_independence": True,
        "secret_reconstruction_when_ordinary_target_leaks": str(leaked_accuracy),
        "conscious_agents_independently_identified": False,
        "brainit_empirical_decoder_recomputed": False,
        "dmt_eeg_fmri_empirical_model_recomputed": False,
        "scope": "Consumer-relative toy contrast only; not a physical interpretation.",
    }


if __name__ == "__main__":
    print(json.dumps(audit(), indent=2, sort_keys=True))
