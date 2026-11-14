import numpy as np

from mobius_bounce_invariant_probe import (
    alpha_spread,
    bounce_action,
    maximum_j_violations,
    mobius_shifted_field,
    same_or_better_invariant,
)


def test_shifted_well_alpha_invariance():
    alphas = np.linspace(0, 2 * np.pi, 33, endpoint=False)
    values = [
        bounce_action(lambda s, a=alpha: mobius_shifted_field(s, a, 0.5), 0.95)
        for alpha in alphas
    ]
    assert alpha_spread(values) < 5e-4


def test_maximum_j_toy_profile():
    alphas = np.linspace(0, 2 * np.pi, 17, endpoint=False)
    radii = [0.2, 0.4, 0.6, 0.8]
    means = []
    for rho in radii:
        values = [
            bounce_action(lambda s, a=alpha, r=rho: mobius_shifted_field(s, a, r), 0.95)
            for alpha in alphas
        ]
        means.append(float(np.mean(values)))
    assert maximum_j_violations(means) == 0


def test_same_or_better_reference():
    candidate = {
        "alpha_spread": 1e-4,
        "maxJ_violations": 0,
        "radial_drift_defect": 0.01,
    }
    reference = {
        "alpha_spread": 2e-4,
        "maxJ_violations": 0,
        "radial_drift_defect": 0.02,
    }
    assert same_or_better_invariant(candidate, reference)


if __name__ == "__main__":
    test_shifted_well_alpha_invariance()
    test_maximum_j_toy_profile()
    test_same_or_better_reference()
    print("ok")
