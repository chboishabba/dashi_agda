#!/usr/bin/env python3
"""Subject-held-out, source-typed DMT TET *synthetic* severe-test adapter.

Reuses scripts.audit_dmt_tet_presence_synthetic: D'Amelio et al. 2026
(bioRxiv preprint doi:10.64898/2026.04.30.721872), original code at
16067a5ff31b7f390381fc5b25b587b1769d9dd1 (15 TET channels, 4s).
Mago et al. (2026, doi:10.1093/nc/niaf069) motivates the M1a rival,
NOT this finite estimator or an empirical result. M0/M1a model labels are
explicit operational *proxies*, not their authors' fitted mechanisms.
DASHI research direction: Johl Brown. Implementation: OpenAI ChatGPT.
No actual data, external agent evidence, or AI analysis of Erowid reports.
"""
from __future__ import annotations

import argparse
import json
from collections import Counter
from fractions import Fraction
from pathlib import Path

from scripts.audit_dmt_tet_presence_synthetic import validate, _number

# Both models have SEVEN binary source-valued coordinates. Matching number of
# strata does not match inductive biases, effective complexity, or fit quality.
M0 = ('dose', 'time', 'general_intensity', 'entity', 'pleasantness', 'unpleasantness', 'anxiety')
M1A = ('dose', 'time', 'general_intensity', 'entity', 'complex_imagery', 'selfhood', 'salience')
FEATURES = {'M0_nuisance_proxy': M0, 'M1a_endogenous_proxy': M1A}


def build_rows(doc):
    threshold, grouped = validate(doc)  # deliberately rejects all human-data modes
    rows = []
    for (person, dose, stage), items in sorted(grouped.items()):
        if stage != 'DMT':
            continue
        ordered = sorted(items, key=lambda sample: sample['time_index'])
        if len(ordered) < 2:
            raise ValueError('Need at least two temporally consecutive DMT samples')
        for before, after in zip(ordered, ordered[1:]):
            if after['time_index'] != before['time_index'] + 1:
                raise ValueError('Missing 4s TET interval')
            # Next reported entity is the response. Past entity is an
            # autoregressive control in BOTH models; exclusively t features
            # determine the t+1 target, without prospective lookahead.
            obs = {'person': person, 'dose': dose,
                   'target': int(_number(after['values']['entity']) >= threshold),
                   'time': int(before['time_index'] >= len(ordered)//2)}
            for feature in set(M0 + M1A) - {'dose', 'time'}:
                obs[feature] = int(_number(before['values'][feature]) >= threshold)
            rows.append(obs)
    if not rows:
        raise ValueError('No temporally resolved DMT source rows')
    return rows


def key(row, columns):
    return tuple(int(row[k] == 40) if k == 'dose' else row[k] for k in columns)


def heldout(rows):
    people = sorted({r['person'] for r in rows})
    if len(people) < 2:
        raise ValueError('Only group-exclusive held-out subjects can be evaluated')
    folds = []
    for held in people:
        train = [r for r in rows if r['person'] != held]
        test = [r for r in rows if r['person'] == held]
        if not train or not test:
            raise ValueError('Missing training or evaluation subject')
        results = {}
        for label, columns in FEATURES.items():
            counts = Counter(key(r, columns) for r in train)
            positives = Counter(key(r, columns) for r in train if r['target'])
            # Training-only global fallback for unseen cells; never use test
            # counts, labels, or per-person normalisation to fit predictions.
            fallback = Fraction(1 + sum(r['target'] for r in train), 2 + len(train))
            error = Fraction()
            probabilities = []
            for r in test:
                k = key(r, columns)
                p = (Fraction(positives[k]+1, counts[k]+2) if counts[k]
                     else fallback)
                probabilities.append(str(p))
                error += (p - r['target'])**2
            results[label] = {'brier_exact': str(error / len(test)),
                              'predictions_exact': probabilities,
                              'unseen_cell_fallback_training_only': True}
        folds.append({'held_out_person': held, 'n_test_transitions': len(test),
                      'models': results})
    return folds


def audit(doc):
    rows = build_rows(doc)
    folds = heldout(rows)
    return {
        'schema': 'dashi-dmt-tet-heldout-synthetic-v1',
        'models': {k: list(v) for k, v in FEATURES.items()},
        'model_capacity_equal_in_all_respects': False,
        'nominal_binary_feature_count_each': 7,
        'split': 'leave-one-person-out; both doses and all stages held out',
        'target': 'next 4s retrospectively reported entity >= predeclared threshold',
        'within_subject_targets_not_independent_samples': True,
        'folds': folds,
        'M1a_full_mechanistic_implementation': False,
        'M1b_observational_ceiling_disproved': False,
        'M2_external_agent_fitted': False,
        'original_human_data_analysed': False,
        'future_information_leakage_allowed': False,
        "source_code_author": "D'Amelio et al. 2026 (bioRxiv preprint)",
    }


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('synthetic_source', type=Path)
    args = parser.parse_args()
    print(json.dumps(audit(json.loads(args.synthetic_source.read_text())), sort_keys=True, indent=2))


if __name__ == '__main__':
    main()
