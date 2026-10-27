#!/usr/bin/env python3
"""Bounded social-delta source/independence cut; entirely SYNTHETIC.

Original empirical sources retain credit:
Rai et al., iScience 28 (2025) 112922, DOI 10.1016/j.isci.2025.112922:
  observed audience delta-band synchronization in social dance (not psi).
Ciminaghi, Rovelli & Balconi, Brain Cognition 196 (2026) 106433,
  DOI 10.1016/j.bandc.2026.106433: source-reported changes including
  frontal delta dissimilarity during moral persuasion (not a remote field).

Finite postselection witness is a local construction inspired by existing
DASHI PR #1258; same-object and independent-unit gates by PR #1253/#1207.
This does not reconstruct any original recording or Hardt outcome.
"""
from __future__ import annotations
from collections import Counter
from fractions import Fraction as Q
from itertools import combinations
import argparse
import json
import unittest

PARTICIPANTS=23
STIMULUS=(1,-1,1,-1,1,-1,1,-1)
HIDDEN=(1,1,-1,-1,-1,-1,1,1)


def correlation(x, y):
    """Exact centered Pearson for nonconstant rational sequences."""
    if len(x)!=len(y) or len(x)<2:
        raise ValueError('incompatible or short time series')
    a,b=map(lambda z:[Q(v) for v in z],(x,y))
    ma=sum(a)/len(a); mb=sum(b)/len(b)
    aa=[v-ma for v in a]; bb=[v-mb for v in b]
    vx=sum(v*v for v in aa); vy=sum(v*v for v in bb)
    if vx==0 or vy==0:
        raise ValueError('constant signal, correlation undefined')
    cov=sum(x*y for x,y in zip(aa,bb))
    # This toy only uses exact +-1 cases; return normalized squared
    # correlation plus sign (no square roots needed).
    square=cov*cov/(vx*vy)
    if square>1:
        raise ArithmeticError('invalid Cauchy bound')
    return {'sign':1 if cov>0 else -1 if cov<0 else 0,
            'r_squared':str(square)}


def source_roots():
    # Separate publication carriers of one first-person Hardt claimant.
    items=[('Hardt 2017 Opinion','Hardt'),('Hardt 2017 author blog','Hardt'),
           ('Hardt 2020 hosted interview','Hardt'),('Hardt creator reel','Hardt')]
    roots={root for _,root in items}
    assert len(items)==4 and len(roots)==1
    return {'carrier_count':len(items),'independent_original_speakers':len(roots),
            'independent_event_witnesses_supplied':0}


def common_cue_fixture(n=PARTICIPANTS):
    if not isinstance(n,int) or isinstance(n,bool) or n<2:
        raise ValueError('need at least two identifiable subjects')
    # All synthetic people hear/see identical rhythmic content, no coupling.
    x={i:STIMULUS for i in range(n)}
    pairs=list(combinations(x,2))
    assert len(pairs)==n*(n-1)//2
    assert all(correlation(x[i],x[j])=={'sign':1,'r_squared':'1'}
               for i,j in pairs)
    # The same shared stimulus in an independent cohort produces the same
    # "pseudo-dyad" correlations. Therefore raw synchrony by itself
    # does not distinguish actual interaction from common sensory cause.
    pseudo=tuple(STIMULUS for _ in range(n))
    assert all(correlation(x[i],pseudo[j])=={'sign':1,'r_squared':'1'}
               for i in x for j in range(n))
    assert len(pairs)==253 if n==23 else True
    return {'participants':n,'dependent_pair_count':len(pairs),
            'independent_participant_count':n,
            'within_group_correlation_squared':'1',
            'pseudo_dyad_correlation_squared':'1',
            'interaction_specific_correlation_advantage':'0',
            'causal_interbrain_channel_detected':False,
            'pair_count_is_independent_trial_count':False}


def hidden_target_fixture():
    """Same X distribution for both T values: I(T;X)=0 in exact toy."""
    joint=Counter(zip(STIMULUS,HIDDEN))
    assert joint=={(a,b):2 for a in (-1,1) for b in (-1,1)}
    assert correlation(STIMULUS,HIDDEN)['r_squared']=='0'
    return {'joint_counts':{f'{a},{b}':joint[a,b] for a in (-1,1)
                            for b in (-1,1)},
            'secret_guess_by_stimulus_best_accuracy':'1/2',
            'conditional_target_information_bits':0,
            'perfectly_synchronous_brains_do_not_identify_secret':True}


def postselection_fixture():
    """Reporting-selected 80% from balanced 20-trial 50% source, no new effect."""
    full=(True,)*10+(False,)*10
    selected=(True,)*8+(False,)*2
    assert Q(sum(full),len(full))==Q(1,2)
    assert Q(sum(selected),len(selected))==Q(4,5)
    assert Counter(selected) <= Counter(full)
    return {'synthetic_complete_trials':20,'complete_hit_fraction':'1/2',
            'synthetic_reported_trials':10,'reported_hit_fraction':'4/5',
            'outcome_or_receiver_modified_by_selection':False,
            'selection_mechanism_is_not_claimed_as_historical_Hardt_mechanism':True}


def admit_experiment(rows):
    """Minimal same-object design gate; not actual data authentication.

    Each independent participant/session contributes ONCE. Event-level
    repeated pair/epoch measurements are not independently randomized units.
    More evidence (original data/permissions/calibration) remains necessary.
    """
    rows=list(rows)
    if not rows:
        raise ValueError('missing source observations')
    study={(x['source_id'],x['protocol_id'],x['calibration_id'],
            x['target_allocation_hash']) for x in rows}
    if len(study)!=1 or any(not all(k) for k in study):
        raise ValueError('same-source/protocol/calibration/target manifest required')
    ids=[(r['participant_id'],r['session_id']) for r in rows]
    if any(not all(x) for x in ids) or len(set(ids))!=len(ids):
        raise ValueError('duplicate or missing independent participant/session')
    # Repeated sessions from one participant are clustered, NOT additional
    # independently assigned people in this deliberately strict toy gate.
    if len({participant for participant,_ in ids}) != len(ids):
        raise ValueError('repeated participant sessions are not independent people')
    if any(r['record_type']!='one-independent-unit' for r in rows):
        raise ValueError('dyadic pairs or EEG epochs cannot be independent units')
    if any(r.get('blinding')!='sealed' for r in rows):
        raise ValueError('allocation concealment not evidenced')
    return {'syntactic_design_review':True,'independent_units':len(ids),
            'physical_source_and_target_verified':False,
            'causal_anomaly_verified':False}


def example_rows():
    return [dict(source_id='synthetic',protocol_id='toy',
                 calibration_id='not-calibrated',target_allocation_hash='fixture',
                 participant_id=str(i),session_id='session-1',
                 record_type='one-independent-unit',blinding='sealed')
            for i in range(4)]


class TestSocialDeltaCut(unittest.TestCase):
    def test_pair_pseudoreplication(self):
        self.assertEqual(common_cue_fixture()['dependent_pair_count'],253)
    def test_common_stimulus_yoked_control(self):
        self.assertEqual(common_cue_fixture()['interaction_specific_correlation_advantage'],'0')
    def test_secret_independent_of_synchrony(self):
        self.assertEqual(hidden_target_fixture()['conditional_target_information_bits'],0)
    def test_80_percent_postselection_not_causation(self):
        self.assertEqual(postselection_fixture()['reported_hit_fraction'],'4/5')
        self.assertEqual(postselection_fixture()['complete_hit_fraction'],'1/2')
    def test_claimant_root_count(self):
        self.assertEqual(source_roots()['independent_original_speakers'],1)
    def test_cross_protocol_fail_closed(self):
        rows=example_rows();rows[0]['protocol_id']='another-study'
        with self.assertRaisesRegex(ValueError,'same-source'):
            admit_experiment(rows)
    def test_repeated_participant_new_session_rejected(self):
        rows=example_rows();rows[1]['participant_id']=rows[0]['participant_id']
        rows[1]['session_id']='session-2'
        with self.assertRaisesRegex(ValueError,'independent people'):
            admit_experiment(rows)
    def test_epoch_and_dyad_rejected(self):
        rows=example_rows();rows[0]['record_type']='dyad-pair'
        with self.assertRaisesRegex(ValueError,'epochs'):
            admit_experiment(rows)
    def test_duplicate_participant_rejected(self):
        rows=example_rows();rows[1]['participant_id']=rows[0]['participant_id']
        with self.assertRaisesRegex(ValueError,'duplicate'):
            admit_experiment(rows)
    def test_unblinded_rejected(self):
        rows=example_rows();rows[0]['blinding']='open'
        with self.assertRaisesRegex(ValueError,'concealment'):
            admit_experiment(rows)
    def test_design_pass_never_promotes_effect(self):
        self.assertFalse(admit_experiment(example_rows())['causal_anomaly_verified'])
    def test_constant_and_short_correlation_rejected(self):
        with self.assertRaisesRegex(ValueError,'constant'):
            correlation((1,1,1),(1,2,3))
        with self.assertRaisesRegex(ValueError,'short'):
            correlation((1,),(2,))


def main():
    p=argparse.ArgumentParser()
    p.add_argument('--selftest',action='store_true')
    a=p.parse_args()
    if a.selftest:
        suite=unittest.defaultTestLoader.loadTestsFromTestCase(TestSocialDeltaCut)
        result=unittest.TextTestRunner(verbosity=2).run(suite)
        raise SystemExit(0 if result.wasSuccessful() else 1)
    print(json.dumps({'status':'SYNTHETIC_SOURCE_AND_DESIGN_MODEL_ONLY',
                      'source_roots':source_roots(),
                      'common_cue':common_cue_fixture(),
                      'hidden_target':hidden_target_fixture(),
                      'postselection':postselection_fixture()},indent=2,sort_keys=True))

if __name__=='__main__': main()
