#!/usr/bin/env python3
"""YM steelman/BIDI: independently exact nonpromotion counterexamples.

All checks use Fraction, integer finite matrices and explicit witnesses.
These are logical/finite countermodels; NOT SU(N) continuum or Agda receipt.
"""
from fractions import Fraction as Q


def positive_gibbs_does_not_imply_reflection_positivity():
    # Strictly positive, reflection-symmetric 2-state joint Gibbs weights.
    # OS reflection positivity needs the WHOLE crossing Gram form PSD.
    kernel = ((Q(1), Q(2)), (Q(2), Q(1)))
    assert all(w > 0 for row in kernel for w in row)
    assert kernel[0][1] == kernel[1][0]
    test = (Q(1), Q(-1))
    gram = sum(test[i] * kernel[i][j] * test[j]
               for i in range(2) for j in range(2))
    assert gram == Q(-2)
    total = sum(map(sum, kernel))
    assert total == 6 and gram / total == Q(-1, 3)
    return "POSITIVE_WEIGHT_NOT_REFLECTION_POSITIVE"


def finite_gap_does_not_imply_uniform_gap():
    # At cutoff/volume n, Hamiltonian diag(0, 1/n) has positive gap.
    # No common m>0 for all n. The witness n>1/m defeats each proposed m.
    for m in (Q(1), Q(1, 2), Q(1, 17), Q(1, 2026), Q(13, 100)):
        n = m.denominator // m.numerator + 2
        finite_gap = Q(1, n)
        assert finite_gap > 0 and finite_gap < m
    return "EVERY_FINITE_POSITIVE_GAP_NOT_UNIFORM"


def selected_clustering_does_not_imply_global_gap():
    # H_n = diag(0, 1, 1/2, ..., 1/n). OΩ has support only
    # in eigenmode E=1, so the exact spectral Laplace transform
    # <OΩ,e^-tH OΩ> is e^-t for all n, while true gap=1/n -> 0.
    for n in (2, 4, 13, 100):
        modes = [Q(1, k) for k in range(1, n + 1)]
        test_weights = [Q(1)] + [Q(0)] * (n - 1)
        assert min(modes) == Q(1, n)
        for degree in range(7):
            assert sum(w * e ** degree for w, e in zip(test_weights, modes)) == 1
    return "ONE_OBSERVABLE_DECAY_NOT_FULL_OS_SPECTRAL_GAP"


def constant_test_is_not_measure_uniqueness():
    # Integral of constant=1 agrees but measures are unequal.
    mu, nu = (Q(1, 2), Q(1, 2)), (Q(1, 3), Q(2, 3))
    assert sum(mu) == sum(nu) == 1
    test_indicator_first = (Q(1), Q(0))
    assert sum(a * f for a, f in zip(mu, test_indicator_first)) != sum(
        b * f for b, f in zip(nu, test_indicator_first))
    # Conversely, on a finite discrete measurable carrier,
    # agreement on *every* indicator is exactly measure equality.
    all_indicator_values = ([mu[i] for i in range(2)],
                            [nu[i] for i in range(2)])
    assert all_indicator_values[0] != all_indicator_values[1]
    return "ALL_INDICATORS_NEEDED_FOR_PUSHFORWARD_MEASURE_EQUALITY"


def native_c3_label_permutation_not_weighted_invariance():
    # Any cyclic label permutation preserves uniform counting measure.
    # Physical Gibbs invariance also requires literal Wilson action
    # covariance: non-invariant chosen weights refute the converse.
    weights = (Q(1), Q(2), Q(3))
    c3 = (1, 2, 0)
    assert [c3[c3[c3[i]]] for i in range(3)] == list(range(3))
    assert sum(weights) == sum(weights[c3[i]] for i in range(3))
    first_indicator = (Q(1), Q(0), Q(0))
    left = sum(weights[i] * first_indicator[i] for i in range(3))
    right = sum(weights[c3[i]] * first_indicator[i] for i in range(3))
    assert left == 1 and right == 2
    return "HAAR_LABEL_C3_NOT_WEIGHTED_WILSON_C3"


def one_gauge_group_does_not_supply_all_groups():
    # Logical forall-G closure requires a fixed physical scope and
    # witnesses for all compact simple G, not a single selected G.
    checked = {"G_selected": True, "G_other": False}
    assert checked["G_selected"] and not all(checked.values())
    return "SINGLE_GROUP_GAP_NOT_ALL_COMPACT_SIMPLE_GROUPS"


def main():
    tests = [
        positive_gibbs_does_not_imply_reflection_positivity,
        finite_gap_does_not_imply_uniform_gap,
        selected_clustering_does_not_imply_global_gap,
        constant_test_is_not_measure_uniqueness,
        native_c3_label_permutation_not_weighted_invariance,
        one_gauge_group_does_not_supply_all_groups,
    ]
    for test in tests:
        print("PASS:", test())
    print("6/6 exact mathematical negative controls.")
    print("REFERENCE ONLY: not proof of continuum YM/Clay or Agda typechecking.")


if __name__ == "__main__":
    main()
