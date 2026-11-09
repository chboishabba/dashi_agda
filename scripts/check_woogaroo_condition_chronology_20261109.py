#!/usr/bin/env python3
"""Conditional EPBC 2019/8575 C24/C25 timeline evidence join.

Consumes a manifest of *independently authenticated* dates. It does NOT
verify that authentication; unverified or missing facts remain unresolved.
Temporal order is not a full legal compliance determination. No network.
"""
import argparse
import json
import hashlib
import tempfile
from datetime import date
from pathlib import Path


def parsed(item, name, root):
    if not isinstance(item, dict):
        return None, f'{name}: no event receipt'
    # 'authenticated' is a manifest assertion, not an external authentication.
    # Reject a naked true flag unless it is backed by local source bytes.
    if item.get('authenticated') is not True:
        return None, f'{name}: independently reviewed evidence not asserted'
    relative = item.get('source_file')
    claimed_hash = item.get('sha256')
    if not isinstance(relative, str) or not relative.strip():
        return None, f'{name}: source file absent'
    if (not isinstance(claimed_hash, str) or len(claimed_hash) != 64 or
            any(c not in '0123456789abcdef' for c in claimed_hash)):
        return None, f'{name}: valid SHA-256 absent'
    candidate = (root / relative).resolve()
    if not candidate.is_relative_to(root.resolve()):
        return None, f'{name}: source path outside manifest directory'
    if not candidate.is_file() or candidate.stat().st_size == 0:
        return None, f'{name}: original source bytes absent'
    hasher = hashlib.sha256()
    with candidate.open('rb') as stream:
        for block in iter(lambda: stream.read(1024 * 1024), b''):
            hasher.update(block)
    if hasher.hexdigest() != claimed_hash:
        return None, f'{name}: source digest mismatch'
    raw = item.get('date')
    if not isinstance(raw, str):
        return None, f'{name}: date absent'
    try:
        value = date.fromisoformat(raw)
    except ValueError:
        raise ValueError(f'{name}: invalid ISO date')
    if value.isoformat() != raw:
        raise ValueError(f'{name}: date must be canonical YYYY-MM-DD')
    # SHA verification establishes file identity, NOT that the issuer
    # issued it or that the manifest's date was extracted correctly.
    return value, None


def before(declaration, activity, declaration_name, activity_name, condition, root):
    d, d_reason = parsed(declaration, declaration_name, root)
    a, a_reason = parsed(activity, activity_name, root)
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


def audit(data, root=None):
    root = (Path(root) if root is not None else Path.cwd()).resolve()
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
                               'Avonvale VDEC', 'Action commencement', 'C24', root),
        'C24_esk': before(events.get('esk_vdec'), commencement,
                          'Esk VDEC', 'Action commencement', 'C24'),
        'C25_mww': before(events.get('mww_vdec'), outside,
                          'MWW VDEC', 'outside-Phase-One clearing/construction', 'C25', root),
        'C25_does_not_by_itself_require_MWW_before_phase_one': True,
        'chronology_is_not_complete_legal_compliance_proof': True,
        'original_documents_authenticated_by_this_script': False,
        'source_bytes_sha256_verified_before_comparison': True,
        'manifest_event_dates_independently_verified': False,
        'condition_breach_adjudicated': False,
    }


def selftest():
    import copy
    with tempfile.TemporaryDirectory() as tmp:
        root = Path(tmp)
        def event(when, verified=True):
            content = ('SYNTHETIC ' + when).encode()
            file = root / ('source-' + str(len(list(root.iterdir()))) + '.txt')
            file.write_bytes(content)
            return {'date': when, 'authenticated': verified,
                    'source_file': file.name,
                    'sha256': hashlib.sha256(content).hexdigest()}
        base = {'case': 'EPBC 2019/8575', 'events': {
            'action_commencement': event('2026-11-20'),
            'avonvale_vdec': event('2026-11-01'),
            'esk_vdec': event('2026-11-02'),
            'outside_phase_one_first_clearing_or_construction': event('2026-12-15'),
            'mww_vdec': event('2026-12-01')}}
        checks = 0
        good = audit(base, root)
        assert all(good[k]['status'] == 'PRIOR_DATE_SHOWN'
                   for k in ('C24_avonvale', 'C24_esk', 'C25_mww'))
        checks += 1
        assert base['events']['mww_vdec']['date'] > base['events']['action_commencement']['date']
        assert good['C25_mww']['status'] == 'PRIOR_DATE_SHOWN'
        checks += 1
        late = copy.deepcopy(base)
        late['events']['mww_vdec'] = event('2026-12-20')
        assert audit(late, root)['C25_mww']['status'] == 'PRIOR_DATE_NOT_SHOWN'
        checks += 1
        late_esk = copy.deepcopy(base)
        late_esk['events']['esk_vdec'] = event('2026-11-21')
        assert audit(late_esk, root)['C24_esk']['status'] == 'PRIOR_DATE_NOT_SHOWN'
        checks += 1
        same = copy.deepcopy(base)
        same['events']['avonvale_vdec'] = event('2026-11-20')
        assert audit(same, root)['C24_avonvale']['status'] == 'SAME_DAY_ORDER_UNRESOLVED'
        checks += 1
        same_mww = copy.deepcopy(base)
        same_mww['events']['mww_vdec'] = event('2026-12-15')
        assert audit(same_mww, root)['C25_mww']['status'] == 'SAME_DAY_ORDER_UNRESOLVED'
        checks += 1
        unchecked = copy.deepcopy(base)
        unchecked['events']['esk_vdec']['authenticated'] = False
        assert audit(unchecked, root)['C24_esk']['status'] == 'UNRESOLVED_SOURCE'
        checks += 1
        missing = copy.deepcopy(base)
        del missing['events']['outside_phase_one_first_clearing_or_construction']
        assert audit(missing, root)['C25_mww']['status'] == 'UNRESOLVED_SOURCE'
        checks += 1
        wrong = copy.deepcopy(base)
        wrong['case'] = 'EPBC 2018/8347'
        try:
            audit(wrong, root)
            raise AssertionError('wrong case accepted')
        except ValueError:
            pass
        checks += 1
        invalid = copy.deepcopy(base)
        invalid['events']['mww_vdec'] = event('2026-13-01')
        try:
            audit(invalid, root)
            raise AssertionError('invalid date accepted')
        except ValueError:
            pass
        checks += 1
        naked = copy.deepcopy(base)
        del naked['events']['avonvale_vdec']['source_file']
        assert audit(naked, root)['C24_avonvale']['status'] == 'UNRESOLVED_SOURCE'
        checks += 1
        tampered = copy.deepcopy(base)
        tampered['events']['esk_vdec']['sha256'] = '0' * 64
        assert audit(tampered, root)['C24_esk']['status'] == 'UNRESOLVED_SOURCE'
        checks += 1
        escape = copy.deepcopy(base)
        escape['events']['mww_vdec']['source_file'] = '../outside.txt'
        assert audit(escape, root)['C25_mww']['status'] == 'UNRESOLVED_SOURCE'
        checks += 1
        fake = copy.deepcopy(base)
        fake['events']['mww_vdec']['source_file'] = 'missing.txt'
        assert audit(fake, root)['C25_mww']['status'] == 'UNRESOLVED_SOURCE'
        checks += 1
        assert checks == 14
        return {'tests': checks, 'passed': checks, 'synthetic_only': True,
                'original_vdec_or_commencement_receipts_acquired': False,
                'independent_issuer_authentication_performed': False}


def main():
    p = argparse.ArgumentParser()
    p.add_argument('--manifest', type=Path)
    p.add_argument('--out', type=Path)
    p.add_argument('--self-test', action='store_true')
    args = p.parse_args()
    if args.self_test:
        result = selftest()
    elif args.manifest:
        result = audit(json.loads(args.manifest.read_text(encoding='utf-8')), args.manifest.resolve().parent)
    else:
        p.error('provide --manifest or --self-test')
    value = json.dumps(result, indent=2, sort_keys=True) + '\n'
    if args.out:
        args.out.write_text(value, encoding='utf-8')
    print(value, end='')


if __name__ == '__main__':
    main()
