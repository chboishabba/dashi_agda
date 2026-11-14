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


def test_majorization_strengthens_temporal_gap_on_exhaustive_count_pairs():
    for k in (2, 3, 4):
        all_counts = list(product((1, 2, 3, 4), repeat=k))
        for a in all_counts:
            for b in all_counts:
                if sum(a) != sum(b) or not H.multiset_count_majorizes(a, b):
                    continue
                a_gap, b_gap = H.majorization_heaps_temporal_gap_certificate(a, b)
                assert a_gap >= b_gap
                # Independently computed weighted-surplus identity.
                aa = sorted(a, reverse=True)
                assert a_gap == sum((k-i-1)*(aa[i]-1) for i in range(k))


def test_majorization_is_partial_not_universal_or_numerology():
    # Sorted (5,2,2) and (4,4,1) are incomparable: top1 higher on left,
    # top2 higher on right.
    assert not H.multiset_count_majorizes((5,2,2), (4,4,1))
    assert not H.multiset_count_majorizes((4,4,1), (5,2,2))
    assert H.majorization_heaps_temporal_gap_certificate((6,2,1), (3,3,3))[0] > 0
    with pytest.raises(ValueError):
        H.majorization_heaps_temporal_gap_certificate((5,2,2), (4,4,1))
    with pytest.raises(ValueError): H.multiset_count_majorizes((3,2), (3,2,1))
