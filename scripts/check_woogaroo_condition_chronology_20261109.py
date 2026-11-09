#!/usr/bin/env python3
"""Conditional EPBC 2019/8575 C24/C25 timeline evidence join.

Consumes a manifest of *independently authenticated* dates. It does NOT
verify that authentication; unverified or missing facts remain unresolved.
Temporal order is not a full legal compliance determination. No network.
"""
import argparse
import json
from datetime import date
from pathlib import Path


def parsed(item, name):
    if not isinstance(item, dict):
        return None, f'{name}: no event receipt'
    if item.get('authenticated') is not True:
        return None, f'{name}: independent authentication absent'
    raw = item.get('date')
    if not isinstance(raw, str):
        return None, f'{name}: date absent'
    try:
        value = date.fromisoformat(raw)
    except ValueError:
        raise ValueError(f'{name}: invalid ISO date')
    if value.isoformat() != raw:
        raise ValueError(f'{name}: date must be canonical YYYY-MM-DD')
    return value, None


def before(declaration, activity, declaration_name, activity_name, condition):
    d, d_reason = parsed(declaration, declaration_name)
    a, a_reason = parsed(activity, activity_name)
    missing = [x for x in (d_reason, a_reason) if x]
    if missing:
        return {'condition': condition, 'status': 'UNRESOLVED_SOURCE',
                'missing': missing, 'temporal_comparison_only': True}
    return {'condition': condition,
            'date_granularity_only': True,
            'status': ('PRIOR_DATE_SHOWN' if d < a else
                       'SAME_DAY_ORDER_UNRESOLVED' if d == a else
                       'PRIOR_DATE_NOT_SHOWN'),
            'declaration_date': d.isoformat(), 'activity_date': a.isoformat(),
            'temporal_comparison_only': True}


def audit(data):
    if data.get('case') != 'EPBC 2019/8575':
        raise ValueError('Wrong EPBC case')
    events = data.get('events')
    if not isinstance(events, dict):
        raise ValueError('events must be a dictionary')
    commencement = events.get('action_commencement')
    outside = events.get('outside_phase_one_first_clearing_or_construction')
    return {
        'case': 'EPBC 2019/8575',
        'C24_avonvale': before(events.get('avonvale_vdec'), commencement,
                               'Avonvale VDEC', 'Action commencement', 'C24'),
        'C24_esk': before(events.get('esk_vdec'), commencement,
                          'Esk VDEC', 'Action commencement', 'C24'),
        'C25_mww': before(events.get('mww_vdec'), outside,
                          'MWW VDEC', 'outside-Phase-One clearing/construction', 'C25'),
        'C25_does_not_by_itself_require_MWW_before_phase_one': True,
        'chronology_is_not_complete_legal_compliance_proof': True,
        'original_documents_authenticated_by_this_script': False,
        'condition_breach_adjudicated': False,
    }


def selftest():
    def event(when, verified=True):
        return {'date': when, 'authenticated': verified}
    base = {'case': 'EPBC 2019/8575', 'events': {
        'action_commencement': event('2026-11-20'),
        'avonvale_vdec': event('2026-11-01'),
        'esk_vdec': event('2026-11-02'),
        'outside_phase_one_first_clearing_or_construction': event('2026-12-15'),
        'mww_vdec': event('2026-12-01')}}
    import copy
    tests = 0
    good = audit(base)
    assert all(good[k]['status'] == 'PRIOR_DATE_SHOWN'
               for k in ('C24_avonvale', 'C24_esk', 'C25_mww'))
    tests += 1
    # MWW declaration after commencement can still precede outside-phase works.
    assert base['events']['mww_vdec']['date'] > base['events']['action_commencement']['date']
    assert good['C25_mww']['status'] == 'PRIOR_DATE_SHOWN'
    tests += 1
    late = copy.deepcopy(base)
    late['events']['mww_vdec'] = event('2026-12-20')
    assert audit(late)['C25_mww']['status'] == 'PRIOR_DATE_NOT_SHOWN'
    tests += 1
    # Later declaration is a negative chronological comparison, not a
    # court/agency finding of a breach.
    late_esk = copy.deepcopy(base)
    late_esk['events']['esk_vdec'] = event('2026-11-21')
    assert audit(late_esk)['C24_esk']['status'] == 'PRIOR_DATE_NOT_SHOWN'
    assert audit(late_esk)['condition_breach_adjudicated'] is False
    tests += 1
    same = copy.deepcopy(base)
    same['events']['avonvale_vdec'] = event('2026-11-20')
    assert audit(same)['C24_avonvale']['status'] == 'SAME_DAY_ORDER_UNRESOLVED'
    tests += 1
    # A same-day declaration may be earlier or later than a works event.
    # A date-only record cannot choose the temporal order.
    same_mww = copy.deepcopy(base)
    same_mww['events']['mww_vdec'] = event('2026-12-15')
    assert audit(same_mww)['C25_mww']['status'] == 'SAME_DAY_ORDER_UNRESOLVED'
    tests += 1
    unverified = copy.deepcopy(base)
    unverified['events']['esk_vdec']['authenticated'] = False
    assert audit(unverified)['C24_esk']['status'] == 'UNRESOLVED_SOURCE'
    tests += 1
    missing = copy.deepcopy(base)
    del missing['events']['outside_phase_one_first_clearing_or_construction']
    assert audit(missing)['C25_mww']['status'] == 'UNRESOLVED_SOURCE'
    tests += 1
    wrong = copy.deepcopy(base)
    wrong['case'] = 'EPBC 2018/8347'
    try:
        audit(wrong)
        raise AssertionError('wrong case accepted')
    except ValueError as exc:
        assert 'case' in str(exc)
    tests += 1
    malformed = copy.deepcopy(base)
    malformed['events']['mww_vdec']['date'] = '2026-13-01'
    try:
        audit(malformed)
        raise AssertionError('invalid date accepted')
    except ValueError as exc:
        assert 'invalid ISO' in str(exc)
    tests += 1
    assert tests == 10
    return {'tests': tests, 'passed': tests, 'synthetic_only': True,
            'real_vdec_or_commencement_receipts_acquired': False}


def main():
    p = argparse.ArgumentParser()
    p.add_argument('--manifest', type=Path)
    p.add_argument('--out', type=Path)
    p.add_argument('--self-test', action='store_true')
    args = p.parse_args()
    if args.self_test:
        result = selftest()
    elif args.manifest:
        result = audit(json.loads(args.manifest.read_text(encoding='utf-8')))
    else:
        p.error('provide --manifest or --self-test')
    value = json.dumps(result, indent=2, sort_keys=True) + '\n'
    if args.out:
        args.out.write_text(value, encoding='utf-8')
    print(value, end='')


if __name__ == '__main__':
    main()
