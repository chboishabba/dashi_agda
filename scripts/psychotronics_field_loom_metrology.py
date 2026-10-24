#!/usr/bin/env python3
"""Field Loom S1: dimensional force prediction and provenance-gated paired residuals.

This is an analysis protocol and synthetic unit tests, NOT a real observation,
calibration, levitation, gravitational measurement or safety certification.
Built on the existing Biot-Savart coil owner; never upgrades physical authority.
"""
import argparse
import hashlib
import json
import math
from pathlib import Path

MU0 = 4e-7 * math.pi
G0 = 9.80665


def field_center(radius_m=.1, spacing_m=.1, turns=100, ampere=1.):
    """Axial B of equal-current thin circular coils at their midpoint [T]."""
    _geometry(radius_m, spacing_m, turns, ampere)
    return MU0 * turns * ampere * radius_m ** 2 / (radius_m ** 2 + (spacing_m / 2) ** 2) ** 1.5


def anti_gradient_center(radius_m=.1, spacing_m=.1, turns=100, ampere=1.):
    """Exact midpoint dBz/dz [T/m], lower coil +I and upper coil -I."""
    _geometry(radius_m, spacing_m, turns, ampere)
    return -3 * MU0 * turns * ampere * radius_m ** 2 * spacing_m / (2 * (radius_m ** 2 + (spacing_m / 2) ** 2) ** 2.5)


def _geometry(radius_m, spacing_m, turns, ampere):
    vals = (radius_m, spacing_m, turns, ampere)
    if not all(math.isfinite(v) for v in vals) or radius_m <= 0 or spacing_m <= 0 or turns < 1:
        raise ValueError('invalid coil geometry or current')


def force_budget(moment_am2=.01, mass_kg=.001):
    if not math.isfinite(moment_am2) or not math.isfinite(mass_kg) or mass_kg <= 0:
        raise ValueError('invalid moment or mass')
    grad = anti_gradient_center()
    weight = mass_kg * G0
    force = moment_am2 * grad
    return {
        'assumed_moment_Am2': moment_am2,
        'assumed_mass_kg': mass_kg,
        'equal_coil_center_B_T': field_center(),
        'anti_coil_center_gradient_T_per_m': grad,
        'ideal_dipole_force_N': force,
        'weight_N': weight,
        'force_to_weight_abs': abs(force) / weight,
        'moment_for_weight_Am2_abs': weight / abs(grad),
        'model': 'fixed permanent point dipole, central gradient only',
        'induced_moment_at_anti_coil_center': 'B(0)=0; fixed-dipole model is inapplicable to an unsaturated induced moment',
        'physical_measurements': 0,
    }


def sha256_file(path):
    h = hashlib.sha256()
    with open(path, 'rb') as f:
        for chunk in iter(lambda: f.read(1024 * 1024), b''):
            h.update(chunk)
    return h.hexdigest()


def _num(row, key, *, nonnegative=False):
    value = row[key]
    if isinstance(value, bool) or not isinstance(value, (int, float)) or not math.isfinite(value):
        raise ValueError('non-finite or nonnumeric ' + key)
    if nonnegative and value < 0:
        raise ValueError('negative uncertainty ' + key)
    return float(value)


def _sha(value):
    return isinstance(value, str) and len(value) == 64 and all(c in '0123456789abcdef' for c in value)


def _readback_receipt(metadata, label):
    """File-byte identity is not independent instrument/source authentication."""
    path = metadata.get(label + '_file')
    expected = metadata.get(label + '_sha256')
    if not isinstance(path, str) or not _sha(expected):
        return False
    try:
        return sha256_file(path) == expected
    except (FileNotFoundError, PermissionError, IsADirectoryError):
        return False


def paired_analysis(record):
    """Paired signed dipole residual; common uncertainty floor cannot average away.

    Independent random errors are assumed between active/sham observations.
    Calibration correlations, systematic errors and uncertain magnetic
    constitutive response require further explicit model/experiment work.
    """
    meta = record['metadata']
    pairs = record['pairs']
    if not isinstance(pairs, list) or not pairs:
        raise ValueError('at least one complete pair required')
    if not isinstance(meta.get('apparatus_id'), str) or not meta['apparatus_id'].strip():
        raise ValueError('missing apparatus identity')
    if not isinstance(meta.get('configuration_revision'), str) or not meta['configuration_revision'].strip():
        raise ValueError('missing configuration revision')
    if meta.get('origin') not in ('synthetic', 'instrument'):
        raise ValueError('origin must be synthetic or instrument')
    seen = set()
    results = []
    for p in pairs:
        pid = p['pair_id']
        if not isinstance(pid, str) or not pid or pid in seen:
            raise ValueError('missing or duplicate pair identity')
        seen.add(pid)
        a, s = p['active'], p['sham']
        m = _num(p, 'moment_am2')
        um = _num(p, 'moment_std_am2', nonnegative=True)
        systematic = _num(p, 'common_systematic_std_n', nonnegative=True)
        ga, gs = _num(a, 'gradient_t_m'), _num(s, 'gradient_t_m')
        fa, fs = _num(a, 'force_n'), _num(s, 'force_n')
        uga, ugs = _num(a, 'gradient_std_t_m', nonnegative=True), _num(s, 'gradient_std_t_m', nonnegative=True)
        ufa, ufs = _num(a, 'force_std_n', nonnegative=True), _num(s, 'force_std_n', nonnegative=True)
        predicted = m * (ga - gs)
        measured = fa - fs
        residual = measured - predicted
        stat_var = ufa ** 2 + ufs ** 2 + (ga - gs) ** 2 * um ** 2 + m ** 2 * (uga ** 2 + ugs ** 2)
        if stat_var <= 0:
            raise ValueError('zero random uncertainty gives unbounded weight')
        results.append({'pair_id': pid, 'measured_delta_force_n': measured,
                        'predicted_dipole_delta_force_n': predicted,
                        'residual_n': residual, 'random_std_n': math.sqrt(stat_var),
                        'common_systematic_std_n': systematic})
    weights = [1 / (p['random_std_n'] ** 2) for p in results]
    mean = sum(w * p['residual_n'] for w, p in zip(weights, results)) / sum(weights)
    random_std = 1 / math.sqrt(sum(weights))
    sys_floor = max(p['common_systematic_std_n'] for p in results)
    total_std = math.hypot(random_std, sys_floor)
    provenance_ok = all(_readback_receipt(meta, k) for k in ('raw_data', 'calibration'))
    run_count = len(set(p.get('session_id') for p in pairs if isinstance(p.get('session_id'), str) and p['session_id']))
    obligations = []
    for k in ('instrument_serial', 'configuration_revision', 'calibration_revision',
              'attributed_original_source', 'model_revision', 'independent_operator'):
        if not isinstance(meta.get(k), str) or not meta[k].strip():
            obligations.append('missing_' + k)
    for k in ('independent_field_map', 'force_calibration', 'thermal_and_vibration_controls',
              'current_power_log', 'blinded_sham', 'independent_replication'):
        if meta.get(k) is not True:
            obligations.append('unverified_' + k)
    if not provenance_ok:
        obligations.append('missing_or_unmatched_original_raw_and_calibration_file_hashes')
    if len(results) < 4 or run_count < 2:
        obligations.append('insufficient_predefined_pair_or_session_coverage')
    if meta['origin'] == 'synthetic':
        obligations.append('synthetic_input_cannot_support_empirical_detection')
    if not isinstance(meta.get('preregistered_model_id'), str) or not meta['preregistered_model_id']:
        obligations.append('missing_preregistered_model_and_analysis')
    return {
        'origin': meta['origin'], 'apparatus_id': meta['apparatus_id'],
        'pair_count': len(results), 'session_count': run_count,
        'paired_results': results, 'weighted_residual_n': mean,
        'random_std_n': random_std, 'undiluted_systematic_floor_n': sys_floor,
        'total_std_n': total_std, 'abs_residual_over_total_std': abs(mean) / total_std,
        'input_bytes_hash_verified': provenance_ok,
        'submission_ready_for_independent_metrology_review': not obligations,
        'unpaid_obligations': obligations,
        'claim_grade': 'model comparison only; no antigravity, anomalous force or detection certified',
    }


def _selftest():
    b = force_budget()
    assert abs(b['equal_coil_center_B_T'] - .0008991762855732129) < 1e-15
    assert abs(b['anti_coil_center_gradient_T_per_m'] + .010790115426878553) < 1e-13
    assert .0109 < b['force_to_weight_abs'] < .0111
    assert .90 < b['moment_for_weight_Am2_abs'] < .92
    p = {'pair_id': 'p1', 'session_id': 's1', 'moment_am2': .01,
         'moment_std_am2': .0001, 'common_systematic_std_n': .000002,
         'active': {'force_n': -.000108, 'force_std_n': 1e-6,
                    'gradient_t_m': b['anti_coil_center_gradient_T_per_m'], 'gradient_std_t_m': .0001},
         'sham': {'force_n': 0., 'force_std_n': 1e-6,
                  'gradient_t_m': 0., 'gradient_std_t_m': .0001}}
    record = {'metadata': {'origin': 'synthetic', 'apparatus_id': 'illustrative',
                           'configuration_revision': 'idealised'}, 'pairs': [p]}
    r = paired_analysis(record)
    assert abs(r['weighted_residual_n']) < 2e-7
    assert not r['submission_ready_for_independent_metrology_review']
    assert 'synthetic_input_cannot_support_empirical_detection' in r['unpaid_obligations']
    doubled = dict(p, pair_id='p2', session_id='s2')
    r2 = paired_analysis({'metadata': record['metadata'], 'pairs': [p, doubled]})
    assert r2['undiluted_systematic_floor_n'] == r['undiluted_systematic_floor_n']
    try:
        paired_analysis({'metadata': record['metadata'], 'pairs': [p, p]})
    except ValueError:
        pass
    else:
        raise AssertionError('duplicate paired identity accepted')
    p_bad = dict(p, active={**p['active'], 'force_std_n': -1})
    try:
        paired_analysis({'metadata': record['metadata'], 'pairs': [p_bad]})
    except ValueError:
        pass
    else:
        raise AssertionError('negative uncertainty accepted')
    print('S1 metrology: analytic field, force/weight, classical null, sham, independent-systematic, provenance and adversarial checks passed (synthetic)')


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--record-json', type=Path, help='local paired run and actual raw-data/calibration file hashes')
    parser.add_argument('--selftest', action='store_true')
    args = parser.parse_args()
    if args.selftest:
        _selftest()
    print(json.dumps(paired_analysis(json.loads(args.record_json.read_text())) if args.record_json else force_budget(), indent=2))
