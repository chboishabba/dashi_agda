"""Independent exhaustive finite multiset checks of all-time Heaps bounds."""
from itertools import permutations, product
from fractions import Fraction as F
from pathlib import Path
import sys
import pytest
sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'scripts'))
import zipf_heaps_bridge as H


def test_extremal_constructors_cover_every_prefix_simultaneously():
    for counts in product((1, 2, 3), repeat=3):
        c = tuple(counts)
        low, high = H.extremal_multiset_token_orders(c)
        target = sorted(i for i, k in enumerate(c) for _ in range(k))
        assert sorted(low) == sorted(high) == target
        lower, upper = H.multiset_heaps_extremal_profiles(c)
        assert H.observed_prefix_diversity(low) == lower
        assert H.observed_prefix_diversity(high) == upper
        assert (lower[0], upper[0]) == (0, 0)
        assert (lower[-1], upper[-1]) == (len(c), len(c))
        assert sum(upper) - sum(lower) == H.multiset_heaps_area_gap(c)


def test_every_permutation_is_within_exact_profile_not_merely_endpoint():
    for c in ((3, 2, 1), (2, 2, 2), (3, 1, 1), (1, 1, 1), (4, 1)):
        lower, upper = H.multiset_heaps_extremal_profiles(c)
        words = set(permutations(tuple(i for i, k in enumerate(c) for _ in range(k))))
        curves = {H.observed_prefix_diversity(word) for word in words}
        assert all(all(lower[t] <= v[t] <= upper[t] for t in range(len(v))) for v in curves)
        assert lower in curves and upper in curves
        assert all(lower[t] == min(v[t] for v in curves) for t in range(len(lower)))
        assert all(upper[t] == max(v[t] for v in curves) for t in range(len(upper)))
        assert H.multiset_heaps_area_gap(c) == max(map(sum, curves)) - min(map(sum, curves))


def test_permutation_ensemble_expectation_necessarily_lies_within_bounds():
    for c in ((4, 1), (3, 2, 1), (1, 1, 1), (2, 2, 2)):
        lower, upper = H.multiset_heaps_extremal_profiles(c)
        for t in range(sum(c)+1):
            assert F(lower[t]) <= H.expected_permutation_vocabulary(c, t) <= F(upper[t])


def test_order_gap_can_be_large_without_changing_zipf_rank_counts():
    counts = (20, 2, 1)
    low, high = H.extremal_multiset_token_orders(counts)
    assert sorted(low) == sorted(high)
    assert H.observed_prefix_diversity(low)[3] == 1
    assert H.observed_prefix_diversity(high)[3] == 3
    assert H.multiset_heaps_area_gap(counts) == 39


def test_single_type_zero_gap_and_equal_ties_deterministic():
    assert H.multiset_heaps_area_gap((20,)) == 0
    assert H.multiset_heaps_area_gap((1, 1, 1)) == 0
    assert H.extremal_multiset_token_orders((2, 2))[0] == (0, 0, 1, 1)
    assert H.extremal_multiset_token_orders((2, 2))[1] == (0, 1, 0, 1)


def test_input_domain_rejects_missing_and_zero_types():
    for c in ((), (2, 0), (True, 1), (1, -1), (1, 1.0)):
        with pytest.raises(ValueError): H.extremal_multiset_token_orders(c)
        with pytest.raises(ValueError): H.multiset_heaps_area_gap(c)
