#!/usr/bin/env python3
"""P0-A sensitivity of individualized alpha-window selection under a synthetic null.

Original experimental idea: Wang et al. (2019) eNeuro,
DOI 10.1523/ENEURO.0483-18.2019.
This is a DASHI independent mathematical/simulation extension, not original
EEG analysis or numerical reproduction. In real data wavelet correlations,
preprocessing, masking and signal/nonstationarity must be carried separately.
"""
import json
import numpy as np
import sympy as s
from scipy.stats import ttest_1samp


def run(seed=20261122, reps=4000, people=29, windows=40):
    a, b = s.symbols("a b", real=True)
    gap = s.symbols("gap", nonnegative=True)
    minimum = (a + b - s.Abs(a - b)) / 2
    assert s.simplify(minimum.subs(a, b-gap) - (b-gap)) == 0
    assert s.simplify(minimum.subs(a, b+gap) - b) == 0
    sigma = s.symbols("sigma", positive=True)
    expected_min_of_two_independent_normals = -sigma / s.sqrt(s.pi)
    rng = np.random.default_rng(seed)
    # Four conditions x 40 candidate windows per participant, pure noise.
    train = rng.normal(0, 1, size=(reps, people, 4, windows))
    selected_window = np.argmin(train.mean(axis=2), axis=-1)
    in_sample = np.take_along_axis(
        train, selected_window[:, :, None, None], axis=-1
    ).squeeze(-1)
    held = rng.normal(0, 1, size=(reps, people, 4, windows))
    crossfit = np.take_along_axis(
        held, selected_window[:, :, None, None], axis=-1
    ).squeeze(-1)
    # Matched ActiveSweep - ActiveFixed - ShamSweep + ShamFixed.
    vector = np.array([1, -1, -1, 1], dtype=float)
    inter_train = in_sample @ vector
    inter_test = crossfit @ vector
    p_train = ttest_1samp(inter_train, 0, axis=1).pvalue
    p_test = ttest_1samp(inter_test, 0, axis=1).pvalue
    result = {
        "status": "PASS",
        "evidence": "SYNTHETIC_IID_GAUSSIAN_NULL_ONLY",
        "seed": seed, "reps": reps, "people_per_replicate": people,
        "candidate_windows": windows,
        "exact_expected_min_two_normal_windows_unit_sigma":
            str(expected_min_of_two_independent_normals.subs(sigma, 1)),
        "mean_power_training_selected": round(float(in_sample.mean()), 5),
        "mean_power_independent_selected": round(float(crossfit.mean()), 5),
        "mean_interaction_training": round(float(inter_train.mean()), 5),
        "mean_interaction_heldout": round(float(inter_test.mean()), 5),
        "null_rejection_fraction_training_p_below_005":
            round(float((p_train < .05).mean()), 4),
        "null_rejection_fraction_heldout_p_below_005":
            round(float((p_test < .05).mean()), 4),
        "warning": (
            "Negative mean from searching minima does NOT by itself establish "
            "a biased condition interaction; balance and exchangeability are "
            "crucial, and real trial-level EEG remains untested."
        ),
    }
    assert result["mean_power_training_selected"] < -.1
    assert abs(result["mean_power_independent_selected"]) < .04
    assert abs(result["mean_interaction_training"]) < .04
    assert abs(result["mean_interaction_heldout"]) < .04
    assert abs(result["null_rejection_fraction_training_p_below_005"] - .05) < .025
    assert abs(result["null_rejection_fraction_heldout_p_below_005"] - .05) < .025
    print(json.dumps(result, indent=2))
    return result


if __name__ == "__main__":
    run()
