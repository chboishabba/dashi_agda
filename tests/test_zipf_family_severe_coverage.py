"""Exact repo-bound 27-subject acceptance and two original-source repairs."""
from fractions import Fraction as F
from itertools import combinations, product
from pathlib import Path
import sys
import pytest
sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'scripts'))
import zipf_family_severe_coverage as S


def test_all_27_requested_topics_are_live_callable_receipts():
    keys = S.audit_coverage_contract()
    assert len(keys) == len(set(keys)) == 27
    assert keys[0] == 'zipf' and keys[-2:] == ('zipf_mandelbrot', 'hurwitz')


def test_reader_vs_inactive_is_not_a_false_lurker_identity():
    # 1 creator, 1 commenter, 1 measured reader, 1 inactive account.
    assert S.measured_participation_four_tiers([1, 0, 1, 0], [0, 1, 0, 0], [1, 0, 0, 0]) == (F(1,4),)*4
    assert S.measured_participation_four_tiers([0,0], [0,0], [0,0]) == (0,0,0,1)
    assert S.measured_participation_four_tiers([1,1], [0,0], [0,0]) == (0,0,1,0)


def test_actual_observed_90_9_1_distribution_is_constructible_not_forced():
    reads = [1]*100
    comments = [0]*90 + [1]*9 + [0]
    creations = [0]*99 + [1]
    assert S.measured_participation_four_tiers(reads, comments, creations) == (F(1,100),F(9,100),F(90,100),F(0))
    assert S.measured_participation_four_tiers([1]*100, [0]*100, [0]*100) != (F(1,100),F(9,100),F(90,100),F(0))


def test_participation_domain_and_no_false_read_inference():
    with pytest.raises(ValueError): S.measured_participation_four_tiers([],[],[])
    with pytest.raises(ValueError): S.measured_participation_four_tiers([1],[1,0],[0])
    with pytest.raises(ValueError): S.measured_participation_four_tiers([1],[-1],[0])
    with pytest.raises(ValueError): S.measured_participation_four_tiers([True],[0],[0])


def test_bradford_ties_are_never_split_by_tie_preserving_policy():
    counts = [10,5,5,3,3,1]
    rows = S.bradford_tie_preserving_zones(counts,3)
    assert rows == ((1,10),(2,10),(3,7))
    ranked=sorted(counts,reverse=True);cuts=[];position=0
    for size,article_count in rows[:-1]:
        position+=size
        assert ranked[position-1]!=ranked[position]
        cuts.append(position)
    assert cuts == [1,3]


def test_bradford_insufficient_tie_blocks_fails_closed():
    with pytest.raises(ValueError): S.bradford_tie_preserving_zones([2,2,2],2)
    with pytest.raises(ValueError): S.bradford_tie_preserving_zones([0,0,0],1)
    with pytest.raises(ValueError): S.bradford_tie_preserving_zones([1],0)
    assert S.bradford_tie_preserving_zones([4,4,4],1) == ((3,12),)


def test_bradford_tie_dp_matches_independent_exhaustive_search():
    for values in product((0,1,2,4), repeat=4):
        if not any(values): continue
        sorted_values=sorted(values,reverse=True)
        allowed=[i for i in range(1,len(values)) if sorted_values[i-1]!=sorted_values[i]]
        for z in range(1,len(allowed)+2):
            options=[];total=sum(values)
            for cuts in combinations(allowed,z-1):
                endpoints=(0,)+cuts+(len(values),)
                rows=tuple((endpoints[i+1]-endpoints[i],sum(sorted_values[endpoints[i]:endpoints[i+1]])) for i in range(z))
                score=sum((z*a-total)**2 for _,a in rows)
                options.append((score,cuts,rows))
            assert options
            assert S.bradford_tie_preserving_zones(values,z) == min(options) [2]


def test_bradford_tie_and_unrestricted_are_distinct_valid_conventions():
    from zipf_family_coverage_gates import bradford_optimal_equal_zones
    counts=[8,4,4,4,1]
    tied=S.bradford_tie_preserving_zones(counts,2)
    unrestricted=bradford_optimal_equal_zones(counts,2)
    assert sum(n for n,_ in tied) == sum(n for n,_ in unrestricted) == len(counts)
    # The unconstrained optimizer may split the block of three four-article journals.
    cut=unrestricted[0][0]
    assert sorted(counts,reverse=True)[cut-1] == sorted(counts,reverse=True)[cut]
    assert tied != unrestricted
