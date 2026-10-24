#!/usr/bin/env python3
"""DASHI synthetic paired-correctness counterexample, NOT Sophontic data.
Two models pass one premise-change pair; nuisance and action tests separate them.
This is not evidence for or against a company's unreleased model.
"""
from __future__ import annotations

from enum import Enum
import hashlib
import json


class Prompt(Enum):
    CANONICAL = "premise_positive"
    PERTURBED = "premise_negative"
    ANNOTATED_CANONICAL = "premise_positive_with_irrelevant_annotation"
    ANNOTATED_PERTURBED = "premise_negative_with_irrelevant_annotation"


REFERENCE = {
    Prompt.CANONICAL: False,
    Prompt.PERTURBED: True,
    Prompt.ANNOTATED_CANONICAL: False,
    Prompt.ANNOTATED_PERTURBED: True,
}

# Perfect on the paired examples but incorrect on a held-out nuisance variant.
MEMORISED_PAIR = {
    Prompt.CANONICAL: False,
    Prompt.PERTURBED: True,
    Prompt.ANNOTATED_CANONICAL: False,
    Prompt.ANNOTATED_PERTURBED: False,
}

FACT_SENSITIVE = dict(REFERENCE)

FLIP = {
    Prompt.CANONICAL: Prompt.PERTURBED,
    Prompt.PERTURBED: Prompt.CANONICAL,
    Prompt.ANNOTATED_CANONICAL: Prompt.ANNOTATED_PERTURBED,
    Prompt.ANNOTATED_PERTURBED: Prompt.ANNOTATED_CANONICAL,
}


def paired_correct(model):
    return (model[Prompt.CANONICAL] == REFERENCE[Prompt.CANONICAL]
            and model[Prompt.PERTURBED] == REFERENCE[Prompt.PERTURBED])


def nuisance_accuracy(model):
    xs = (Prompt.ANNOTATED_CANONICAL, Prompt.ANNOTATED_PERTURBED)
    return sum(model[x] == REFERENCE[x] for x in xs) / len(xs)


def flip_equivariance(model):
    return sum(model[FLIP[x]] != model[x] for x in Prompt) / len(Prompt)


def nuisance_stability(model):
    return (int(model[Prompt.CANONICAL] == model[Prompt.ANNOTATED_CANONICAL])
            + int(model[Prompt.PERTURBED] == model[Prompt.ANNOTATED_PERTURBED])) / 2


def paired_observation(model):
    return [model[Prompt.CANONICAL], model[Prompt.PERTURBED]]


def audit():
    models = {"memorised_pair": MEMORISED_PAIR, "fact_sensitive": FACT_SENSITIVE}
    results = {
        name: {
            "paired_correct": paired_correct(m),
            "paired_observation": paired_observation(m),
            "nuisance_accuracy": nuisance_accuracy(m),
            "nuisance_stability": nuisance_stability(m),
            "flip_equivariance": flip_equivariance(m),
        } for name, m in models.items()
    }
    fixture = json.dumps({
        "reference": {x.value: REFERENCE[x] for x in Prompt},
        "memorised": {x.value: MEMORISED_PAIR[x] for x in Prompt},
        "fact_sensitive": {x.value: FACT_SENSITIVE[x] for x in Prompt},
    }, sort_keys=True, separators=(",", ":")).encode()
    return {
        "kind": "DASHI_SYNTHETIC_COUNTEREXAMPLE_NOT_SOPHONTIC_MODEL_EVAL",
        "fixture_sha256": hashlib.sha256(fixture).hexdigest(),
        "n_prompt_states": len(Prompt),
        "paired_observer_collision": (
            paired_observation(MEMORISED_PAIR) == paired_observation(FACT_SENSITIVE)),
        "heldout_nuisance_separates": (
            nuisance_accuracy(MEMORISED_PAIR) != nuisance_accuracy(FACT_SENSITIVE)),
        "models": results,
    }


def self_test():
    r = audit()
    m = r["models"]
    assert r["paired_observer_collision"] and r["heldout_nuisance_separates"]
    assert m["memorised_pair"]["paired_correct"]
    assert m["fact_sensitive"]["paired_correct"]
    assert m["memorised_pair"]["nuisance_accuracy"] == 0.5
    assert m["fact_sensitive"]["nuisance_accuracy"] == 1.0
    assert m["memorised_pair"]["nuisance_stability"] == 0.5
    assert m["fact_sensitive"]["nuisance_stability"] == 1.0
    assert m["memorised_pair"]["flip_equivariance"] == 0.5
    assert m["fact_sensitive"]["flip_equivariance"] == 1.0
    assert all(FLIP[FLIP[x]] == x for x in Prompt)
    return r


if __name__ == "__main__":
    print(json.dumps(self_test(), indent=2, sort_keys=True))
