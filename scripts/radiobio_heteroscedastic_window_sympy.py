#!/usr/bin/env python3
"""Exact and synthetic P0-A3 heteroscedastic alpha-window selection test.

Original experiment and EEG analysis: Connie X. Wang et al., eNeuro 2019,
DOI 10.1523/ENEURO.0483-18.2019.
This is an independent DASHI mathematical extension; NO original EEG was loaded.
"""
import json
import numpy as np
import sympy as S
from scipy.stats import ttest_1samp

C = S.Matrix([1, -1, -1, 1])
U = S.Matrix([1, 1, 1, 1]) / 4
v = S.symbols("v0:4", positive=True)
V = S.diag(*v)
variance_mean = (U.T * V * U)[0]
cov_interaction_mean = (C.T * V * U)[0]
selected_min_expectation = -S.sqrt(variance_mean) / S.sqrt(S.pi)
selection_bias = S.simplify(
    (cov_interaction_mean / variance_mean) * selected_min_expectation
)
assert S.simplify(
    selection_bias + sum(C[i] * v[i] for i in range(4)) / S.sqrt(S.pi * sum(v))
) == 0
assert S.simplify(selection_bias.subs(dict(zip(v, [1, 1, 1, 1])))) == 0

CASES = {
    "balanced": [1, 1, 1, 1],
    "active_sweep_higher_variance": [4, 1, 1, 1],
    "active_fixed_higher_variance": [1, 4, 1, 1],
    "variance_cancelled_but_heterogeneous": [4, 2, 4, 2],
}


def run(seed=20261122, reps=5000, people=29):
    rng = np.random.default_rng(seed)
    output = {}
    for name, vv in CASES.items():
        scale = np.sqrt(np.asarray(vv))[None, None, None, :]
        # Null: two candidate windows x 4 cells, drawn independently per person.
        train = rng.normal(size=(reps, people, 2, 4)) * scale
        window = np.argmin(train.mean(axis=-1), axis=2)
        selected = np.take_along_axis(
            train, window[:, :, None, None], axis=2
        )[:, :, 0, :]
        holdout = rng.normal(size=(reps, people, 2, 4)) * scale
        independent = np.take_along_axis(
            holdout, window[:, :, None, None], axis=2
        )[:, :, 0, :]
        contrast_selected = selected @ np.asarray(C, dtype=float).ravel()
        contrast_held = independent @ np.asarray(C, dtype=float).ravel()
        exact = S.simplify(selection_bias.subs(dict(zip(v, vv))))
        predicted = float(exact.evalf())
        observed = float(contrast_selected.mean())
        held = float(contrast_held.mean())
        p_selected = ttest_1samp(contrast_selected, 0, axis=1).pvalue
        p_held = ttest_1samp(contrast_held, 0, axis=1).pvalue
        assert abs(observed - predicted) < 0.05, (name, observed, predicted)
        assert abs(held) < 0.05, (name, held)
        output[name] = {
            "variances": vv,
            "exact_mean_bias": str(exact),
            "predicted": round(predicted, 5),
            "selected_mean": round(observed, 5),
            "heldout_mean": round(held, 5),
            "false_positive_rate_selected": round(float((p_selected < .05).mean()), 4),
            "false_positive_rate_heldout": round(float((p_held < .05).mean()), 4),
        }
    result = {
        "status": "PASS", "evidence": "SYNTHETIC_GAUSSIAN_NULL_ONLY",
        "seed": seed, "replications": reps, "people_per_replication": people,
        "candidate_windows": 2, "formula": str(selection_bias),
        "cases": output,
        "boundary": "No claim about observed Wang EEG variance or actual false-positive rate.",
    }
    print(json.dumps(result, indent=2))
    return result


if __name__ == "__main__":
    run()
