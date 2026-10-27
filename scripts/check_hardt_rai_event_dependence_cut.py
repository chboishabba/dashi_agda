#!/usr/bin/env python3
"""Exact *synthetic* Rai 2025 audience-event/dyad dependence discriminator.

Original human study: Rai et al., iScience 28 (2025) 112922,
DOI 10.1016/j.isci.2025.112922. No study EEG is processed here.
Only a hypothetical *performance-level randomized assignment* uses the
three-event sign-randomization calculation; it is NOT Rai's published test.
"""
from __future__ import annotations
import argparse
import json
from fractions import Fraction
from itertools import product
from math import comb
import unittest

PAPER_DOI = '10.1016/j.isci.2025.112922'
REPORTED_LIVE_EVENT_SIZES = (20, 18, 21)
DATA_DOI = '10.5522/04/28508744.v1'


def event_pair_structure(sizes=REPORTED_LIVE_EVENT_SIZES):
    """Combinatorial bound, not independent observations/effective N."""
    if tuple(sizes) != REPORTED_LIVE_EVENT_SIZES or any(type(n) is not int for n in sizes):
        raise ValueError('source-locked original performance counts changed')
    pairs = tuple(comb(n, 2) for n in sizes)
    overlapping_pair_pairs = tuple(n * comb(n - 1, 2) for n in sizes)
    return dict(paper_doi=PAPER_DOI, retained_live_eeg=59,
                independent_live_performance_events=3, published_event_sizes=list(sizes),
                same_event_pair_combinations=list(pairs), pair_combinations=sum(pairs),
                dyad_pair_pairs_sharing_person=sum(overlapping_pair_pairs),
                independent_dyad_samples_claimed=False,
                independent_people_conditional_on_shared_event_proven=False,
                deposit_57_to_paper_59_identity_join_verified=False)


def centred(xs):
    xs = tuple(Fraction(v) for v in xs)
    avg = sum(xs, Fraction(0)) / len(xs)
    return tuple(x - avg for x in xs)


def correlation_squared(xs, ys):
    """Squared Pearson correlation over exact rationals; descriptive only."""
    if len(xs) != len(ys) or len(xs) < 2:
        raise ValueError('unmatched or undersampled time streams')
    x, y = centred(xs), centred(ys)
    xy = sum((a * b for a, b in zip(x, y)), Fraction(0))
    xx = sum((a * a for a in x), Fraction(0))
    yy = sum((b * b for b in y), Fraction(0))
    if xx == 0 or yy == 0:
        raise ValueError('constant sensor series')
    return xy * xy / (xx * yy)


def common_event_witness():
    """All K_n pairs synchronize through common cues; no X_i -> X_j edges.

    For event e, X[e,i,t] = S[e,t] + i with S=e*(-1,0,+1,0).
    Subject-specific constant offset does not change centered correlations.
    The constructed source is external; EEG and neural causality not modelled.
    """
    pairs = 0
    for event, n in enumerate(REPORTED_LIVE_EVENT_SIZES, start=1):
        stimulus = tuple(event * x for x in (-1, 0, 1, 0))
        signals = [tuple(v + i for v in stimulus) for i in range(n)]
        for i in range(n):
            for j in range(i + 1, n):
                assert correlation_squared(signals[i], signals[j]) == 1
                pairs += 1
    return dict(invented_sensors=sum(REPORTED_LIVE_EVENT_SIZES),
                invented_synchronized_same_event_pairs=pairs,
                exact_pairwise_Pearson_R_squared='1',
                direct_interpersonal_edges=0, external_shared_stimulus=True,
                actual_Rai_CCA_computed=False, experimental_result=False)


def exact_event_sign_test(event_effects=(2, 3, 5)):
    """Exact illustrative sharp-null sign randomization by *event*.

    Requires assigned intervention randomized independently at event level,
    symmetry/sharp-null and a prespecified absolute sum statistic. These
    design assumptions are NOT established for the original Rai study.
    """
    effects = tuple(Fraction(x) for x in event_effects)
    if len(effects) != 3 or any(x <= 0 for x in effects):
        raise ValueError('three positive hypothetical event effects required')
    observed = abs(sum(effects))
    null = tuple(abs(sum(s * x for s, x in zip(signs, effects)))
                 for signs in product((-1, 1), repeat=len(effects)))
    extreme = sum(x >= observed for x in null)
    event_p = Fraction(extreme, len(null))
    pair_n = event_pair_structure()['pair_combinations']
    # Invalid comparator: pretending all pairs independently randomized.
    pseudo_p = Fraction(2, 2 ** pair_n)
    return dict(event_assignment_units=3, event_randomization_worlds=len(null),
                observed_absolute_event_sum=str(observed),
                exact_event_level_two_sided_p=str(event_p),
                pseudo_independent_dyad_worlds=str(2 ** pair_n),
                invalid_dyad_level_two_sided_p=str(pseudo_p),
                dyad_sign_randomization_valid_for_event_assignment=False,
                rai_experiment_was_event_randomized=None,
                actual_Rai_permutation_p_recomputed=False,
                causal_sender_receiver_link_verified=False)


def audit():
    return dict(pair_structure=event_pair_structure(), shared_input=common_event_witness(),
                hypothetical_randomization=exact_event_sign_test(),
                original_UCL_eeg_files_ingested=0,
                experimental_units_must_follow_assignment_and_dependence=True,
                performer_to_audience_or_receiver_effect_established=False)


class TestRaiEventDependence(unittest.TestCase):
    def test_performance_counts(self):
        self.assertEqual(event_pair_structure()['published_event_sizes'], [20, 18, 21])
    def test_pair_counts(self):
        self.assertEqual(event_pair_structure()['same_event_pair_combinations'], [190,153,210])
    def test_total_pairs(self):
        self.assertEqual(event_pair_structure()['pair_combinations'], 553)
    def test_overlapping_dyad_pairs(self):
        self.assertEqual(event_pair_structure()['dyad_pair_pairs_sharing_person'], 9858)
    def test_reject_wrong_paper_denominator(self):
        with self.assertRaises(ValueError): event_pair_structure((19,19,21))
    def test_all_553_pairs_without_direct_edges(self):
        r=common_event_witness()
        self.assertEqual(r['invented_synchronized_same_event_pairs'], 553)
        self.assertEqual(r['direct_interpersonal_edges'],0)
    def test_correlation_exact_rational(self):
        self.assertEqual(correlation_squared((0,1,2),(11,12,13)), Fraction(1))
    def test_reject_constant_sensor(self):
        with self.assertRaises(ValueError):correlation_squared((1,1,1),(1,2,3))
    def test_three_event_randomization_worlds(self):
        self.assertEqual(exact_event_sign_test()['event_randomization_worlds'],8)
    def test_correct_event_level_p(self):
        self.assertEqual(Fraction(exact_event_sign_test()['exact_event_level_two_sided_p']), Fraction(1,4))
    def test_naive_dyad_p_must_not_be_used(self):
        r=exact_event_sign_test()
        self.assertEqual(Fraction(r['invalid_dyad_level_two_sided_p']), Fraction(1,2**552))
        self.assertFalse(r['dyad_sign_randomization_valid_for_event_assignment'])
    def test_scope_no_rerun(self):
        self.assertEqual(audit()['original_UCL_eeg_files_ingested'],0)
        self.assertFalse(audit()['hypothetical_randomization']['actual_Rai_permutation_p_recomputed'])


def main():
    parser=argparse.ArgumentParser()
    parser.add_argument('--selftest',action='store_true')
    args=parser.parse_args()
    if args.selftest:
        result=unittest.TextTestRunner(verbosity=2).run(
            unittest.defaultTestLoader.loadTestsFromTestCase(TestRaiEventDependence))
        raise SystemExit(0 if result.wasSuccessful() else 1)
    print(json.dumps(audit(),indent=2,sort_keys=True))


if __name__=='__main__':main()
