"""Independent exact verification of constructive pair-switch S24 coupling.

Rational source file reproduced locally and tested against independent word
enumeration before commit. This is not an Agda kernel proof.
"""
from collections import defaultdict
from fractions import Fraction as F
from itertools import permutations, product
from pathlib import Path
import sys
import pytest

ROOT=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT/"scripts"))
from zipf_s24_pair_switch_constructive_exact import (
    constructive_pair_transfer_path_certificate, pair_switch_truncated_law,
    quantile_ordered_pair_switches, _common_group_schedules
)
from zipf_heaps_bridge import observed_prefix_diversity


def _independent_word_law(counts, horizon, sampler):
    out=defaultdict(F)
    if sampler=="iid":
        words=product(range(len(counts)),repeat=horizon)
        for word in words:
            p=F(1)
            for label in word: p*=F(counts[label],sum(counts))
            out[observed_prefix_diversity(word)]+=p
    else:
        tokens=tuple(i for i,c in enumerate(counts) for _ in range(c))
        words=set(permutations(tokens))
        for word in words:
            out[observed_prefix_diversity(word[:horizon])]+=F(1,len(words))
    return dict(out)


def test_constructive_full_path_against_independent_word_oracle():
    # Each returned coupling contains one ordered pair of complete paths,
    # not a collection of independently coupled one-time marginals.
    cases=((2,2),(3,2),(2,2,1),(3,2,1),(4,2,1),
           (3,3,1),(3,2,2),(3,1,2))
    checked=0
    for counts in cases:
        pair=(0,2) if counts==(3,1,2) else (0,1)
        new=tuple(x+(1 if i==pair[0] else -1 if i==pair[1] else 0)
                  for i,x in enumerate(counts))
        for sampler in ("iid","permutation"):
            for t in range(min(5,sum(counts))+1):
                receipt=constructive_pair_transfer_path_certificate(
                    counts,pair,t,sampler)
                assert receipt.left_law==_independent_word_law(new,t,sampler)
                assert receipt.right_law==_independent_word_law(counts,t,sampler)
                receipt.validate()
                checked+=1
    assert checked==94


def test_more_small_transfer_couplings_both_samplers():
    # All valid positive two-/three-type transfers with counts in {1,2,3}.
    checked=0
    for k in (2,3):
        for counts in product((1,2,3),repeat=k):
            for i in range(k):
                for j in range(k):
                    if i==j or counts[i]<counts[j] or counts[j]<2:continue
                    for sampler in ("iid","permutation"):
                        for horizon in range(min(sum(counts),5)+1):
                            receipt=constructive_pair_transfer_path_certificate(
                                counts,(i,j),horizon,sampler)
                            receipt.validate()
                            checked+=1
    assert checked==716


def test_inverse_cdf_switch_time_coupling_preserves_both_marginals():
    for a,b in ((2,2),(3,2),(4,2),(5,3),(5,5)):
        for sampler in ("iid","permutation"):
            for horizon in range(10):
                original=pair_switch_truncated_law(a,b,horizon,sampler)
                concentrated=pair_switch_truncated_law(a+1,b-1,horizon,sampler)
                transport=quantile_ordered_pair_switches(original,concentrated)
                assert sum(transport.values(),F())==1
                assert all(late>=early for late,early in transport)
                for t,p in concentrated.items():
                    assert sum((v for (x,_),v in transport.items() if x==t),F())==p
                for t,p in original.items():
                    assert sum((v for (_,x),v in transport.items() if x==t),F())==p


def test_common_outer_schedule_normalizes_and_forgets_pair_labels():
    counts=(3,2,1)
    for sampler in ("iid","permutation"):
        for horizon in range(7):
            schedule=_common_group_schedules(counts,(0,1),horizon,sampler)
            assert sum(schedule.values(),F())==1
            assert all(set(seq)<=set((-1,2)) for seq in schedule)
            assert all(len(seq)==horizon for seq in schedule)


def test_invalid_inputs_and_wrong_switch_order_fail_closed():
    for bad_pair in ((0,0),(0,3),(-1,0),(True,1),(0,),[0,1]):
        with pytest.raises(ValueError):
            constructive_pair_transfer_path_certificate(
                (3,2,1),bad_pair,3,"iid")
    for bad_count in ((1,1,1),(2,3,1)):
        with pytest.raises(ValueError):
            constructive_pair_transfer_path_certificate(
                bad_count,(0,1),2,"iid")
    with pytest.raises(ValueError):
        constructive_pair_transfer_path_certificate((3,2,1),(0,1),7,"permutation")
    with pytest.raises(ValueError):
        constructive_pair_transfer_path_certificate((3,2,1),(0,1),False,"iid")
    with pytest.raises(ValueError):
        constructive_pair_transfer_path_certificate((3,2,1),(0,1),2,"made-up")
    with pytest.raises(ValueError):
        quantile_ordered_pair_switches({3:F(1)},{2:F(1)})
    with pytest.raises(ValueError):
        quantile_ordered_pair_switches({2:F(1,2)},{3:F(1)})
    with pytest.raises(ValueError):
        pair_switch_truncated_law(2,1,True,"iid")


def test_consume_existing_canonical_owners_without_a_duplicate_s3_or_pnf():
    src=(ROOT/"scripts/zipf_s24_pair_switch_constructive_exact.py").read_text()
    assert "from zipf_heaps_bridge import _validated_counts" in src
    assert "from zipf_full_heaps_path_distribution_exact import full_heaps_curve_law" in src
    assert "PathTransportCertificate, pair_one_type_survival_probability" in src
    assert "Strassen" in src and "NOT a general Agda kernel proof" in src
