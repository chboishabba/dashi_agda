#!/usr/bin/env python3
"""CCDCOE P3 census check: exact equality with a predeclared article frame.

This verifies only INTERNAL coverage of the submitted, frozen frame. It does not
verify that the frame contains every historical article or that treatment was
assigned independently of outcome. No historical GCC case is admitted here.
"""
import argparse
import json
import hashlib
from collections import Counter
from copy import deepcopy
from pathlib import Path

ARMS = {'GCC-linked-outlet', 'comparison-outlet'}
PERIODS = {'before', 'after'}
SCHEMA = 'dashi.ccdcoe.p3.predeclared_article_frame.v1'


def require(condition, reason):
    if not condition:
        raise ValueError(reason)


def canonical_frame_sha256(frame):
    """Hash the entire declared frame; an independent party must retain the digest."""
    canonical = json.dumps(frame, sort_keys=True, separators=(',', ':'), ensure_ascii=False)
    return hashlib.sha256(canonical.encode('utf-8')).hexdigest()


def check(frame, measured, expected_frame_sha256=None):
    require(isinstance(frame, dict), 'frame must be an object')
    require(frame.get('schema') == SCHEMA, 'frame schema')
    actual_digest = canonical_frame_sha256(frame)
    if expected_frame_sha256 is not None:
        require(isinstance(expected_frame_sha256, str) and
                len(expected_frame_sha256) == 64 and
                all(c in '0123456789abcdef' for c in expected_frame_sha256),
                'expected frame SHA256 must be 64 lowercase hex characters')
        require(actual_digest == expected_frame_sha256,
                'declared article frame differs from committed SHA256')
    require(frame.get('frozen_before_coding') is True, 'frame must be frozen before coding')
    for name in ('frame_id', 'inclusion_rule', 'exclusion_rule', 'frame_provenance'):
        require(isinstance(frame.get(name), str) and frame[name].strip(), 'frame field: ' + name)
    units = frame.get('units')
    require(isinstance(units, list) and units, 'nonempty predeclared frame')
    registered = {}
    eligible = set()
    excluded = set()
    expected_cells = {(a, p) for a in ARMS for p in PERIODS}
    for u in units:
        require(isinstance(u, dict), 'unit object')
        uid = u.get('id')
        require(isinstance(uid, str) and uid.strip(), 'unit id')
        require(uid not in registered, 'duplicate original unit in frame')
        require(u.get('arm') in ARMS and u.get('period') in PERIODS, 'invalid arm/period')
        require(type(u.get('eligible')) is bool, 'eligibility must be boolean')
        if u['eligible']:
            require(u.get('exclusion_reason') in (None, ''), 'eligible unit has exclusion')
            eligible.add(uid)
        else:
            require(isinstance(u.get('exclusion_reason'), str) and u['exclusion_reason'].strip(),
                    'excluded unit must have reason')
            excluded.add(uid)
        registered[uid] = u
    require({(u['arm'], u['period']) for u in units if u['eligible']} == expected_cells,
            'missing eligible treatment-period cell')
    require(isinstance(measured, list), 'measured observations list')
    observed = {}
    for m in measured:
        require(isinstance(m, dict), 'measured object')
        uid = m.get('id')
        require(isinstance(uid, str) and uid.strip(), 'measured id')
        require(uid not in observed, 'duplicate measured original unit')
        require(uid in registered, 'measurement not in declared frame')
        require(uid in eligible, 'excluded unit measured as eligible')
        u = registered[uid]
        require(m.get('treatment') == u['arm'] and m.get('period') == u['period'],
                'measurement arm/period differs from frozen frame')
        observed[uid] = m
    require(set(observed) == eligible, 'missing eligible original articles from measurements')
    counts = Counter((registered[uid]['arm'], registered[uid]['period']) for uid in eligible)
    return {'schema': SCHEMA, 'frame_id': frame['frame_id'],
            'canonical_frame_sha256': actual_digest,
            'frame_commitment_checked': expected_frame_sha256 is not None,
            'declared_units': len(units), 'eligible_units': len(eligible),
            'excluded_units': len(excluded), 'measured_eligible_units': len(observed),
            'four_cell_eligible_denominators': {a + ':' + p: counts[a, p]
                                               for a, p in sorted(expected_cells)},
            'frame_coverage_relative_to_declared_units': True,
            'historical_population_completeness_verified': False,
            'exclusion_independent_of_outcome_verified': False,
            'causal_effect_identified': False}


def self_test():
    units = [{'id': f'{a}:{p}', 'arm': a, 'period': p, 'eligible': True}
             for a in sorted(ARMS) for p in sorted(PERIODS)]
    units.append({'id': 'excluded', 'arm': 'comparison-outlet', 'period': 'before',
                  'eligible': False, 'exclusion_reason': 'predeclared out-of-scope edition'})
    frame = {'schema': SCHEMA, 'frame_id': 'SYNTHETIC-ONLY',
             'frozen_before_coding': True, 'inclusion_rule': 'fixture rule',
             'exclusion_rule': 'fixture exclusions', 'frame_provenance': 'fixture',
             'units': units}
    measured = [{'id': u['id'], 'treatment': u['arm'], 'period': u['period']}
                for u in units if u['eligible']]
    good = check(frame, measured)
    assert good['eligible_units'] == 4 and good['excluded_units'] == 1
    committed = canonical_frame_sha256(frame)
    assert check(frame, measured, committed)['frame_commitment_checked'] is True
    altered = deepcopy(frame)
    altered['inclusion_rule'] = 'post-hoc altered rule'
    try:
        check(altered, measured, committed)
    except ValueError as error:
        assert 'differs from committed SHA256' in str(error)
    else:
        raise AssertionError('Post-hoc change of frozen frame was accepted')
    try:
        check(frame, measured, '0' * 63)
    except ValueError as error:
        assert '64 lowercase hex' in str(error)
    else:
        raise AssertionError('Malformed commitment was accepted')
    cases = [
        ('unfrozen', lambda f, m: f.update(frozen_before_coding='true'), 'frame must be frozen'),
        ('missing', lambda f, m: m.pop(), 'missing eligible original articles'),
        ('extra', lambda f, m: m.append({'id': 'unregistered', 'treatment': m[0]['treatment'], 'period': m[0]['period']}), 'not in declared frame'),
        ('duplicate', lambda f, m: m.append(dict(m[0])), 'duplicate measured original unit'),
        ('excluded', lambda f, m: m.append({'id': 'excluded', 'treatment': 'comparison-outlet', 'period': 'before'}), 'excluded unit measured'),
        ('arm_flip', lambda f, m: m[0].update(treatment='comparison-outlet' if m[0]['treatment'] == 'GCC-linked-outlet' else 'GCC-linked-outlet'), 'differs from frozen frame'),
        ('eligibility_string', lambda f, m: f['units'][0].update(eligible='false'), 'eligibility must be boolean'),
        ('no_exclusion_reason', lambda f, m: f['units'][-1].update(exclusion_reason=' '), 'excluded unit must have reason'),
        ('duplicate_frame', lambda f, m: f['units'].append(dict(f['units'][0])), 'duplicate original unit'),
        ('missing_cell', lambda f, m: [u.update(eligible=False, exclusion_reason='frozen exclusion') for u in f['units'][:1]], 'missing eligible treatment-period cell'),
    ]
    for name, mutate, message in cases:
        f, m = deepcopy(frame), deepcopy(measured)
        mutate(f, m)
        try:
            check(f, m)
        except ValueError as error:
            assert message in str(error), (name, str(error))
        else:
            raise AssertionError(name + ' should fail')
    return {'positive_synthetic_frame': True, 'targeted_negative_controls': len(cases) + 2,
            'historical_articles_admitted': 0}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--self-test', action='store_true')
    parser.add_argument('--frame', type=Path)
    parser.add_argument('--measurements', type=Path)
    parser.add_argument('--expected-frame-sha256', required=False)
    args = parser.parse_args()
    if args.self_test:
        print(json.dumps(self_test(), indent=2))
        return
    if args.frame is None or args.measurements is None or args.expected_frame_sha256 is None:
        parser.error('--frame JSON, --measurements JSONL and --expected-frame-sha256 are required')
    frame = json.loads(args.frame.read_text(encoding='utf-8'))
    rows = [json.loads(line) for line in args.measurements.read_text(encoding='utf-8').splitlines() if line.strip()]
    print(json.dumps(check(frame, rows, args.expected_frame_sha256), indent=2))


if __name__ == '__main__':
    main()
