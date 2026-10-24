#!/usr/bin/env python3
"""Deterministic S1 CSV sensor-stream -> pair replay (SI, schema v1).

The source stream and calibration bytes are supplied by the hash-verifying
source-join owner. Replay proves a *content relationship*, not that the
instrument, its timestamps, polarities, calibrations or operator are authentic.
"""
import csv
import io
import math

COLUMNS = ('pair_id', 'session_id', 'condition', 'time_ns', 'coil_current_a',
           'dipole_sign', 'force_n', 'gradient_t_m', 'moment_calibration_id')
VERSION = 'S1-CSV-v1'
MAX_ROWS = 20000


def _finite(value, label):
    try:
        x = float(value)
    except (ValueError, TypeError, OverflowError) as exc:
        raise ValueError('invalid ' + label) from exc
    if not math.isfinite(x):
        raise ValueError('nonfinite ' + label)
    return x


def _nonnegative(value, label, positive=False):
    x = _finite(value, label)
    if (positive and x <= 0) or (not positive and x < 0):
        raise ValueError('negative or zero ' + label)
    return x


def replay_si_csv(stream_bytes, raw, cal):
    """Return {pairs, factorial_settings, row_count, reducer_version}.

    Each independent *pair* uses two signed current/gradient/force samples
    with the same session, dipole orientation and moment calibration ID.
    A calibration is shared by its ID; repeating pairs cannot erase it.
    """
    if raw.get('pair_to_stream_reducer') != VERSION or raw.get('stream_unit_convention') != 'SI':
        raise ValueError('reducer version and SI units must be explicit')
    groups = cal.get('moment_calibration_groups')
    if not isinstance(groups, dict) or not groups:
        raise ValueError('missing moment calibration groups')
    force_std = _nonnegative(cal.get('force_readout_std_n'), 'force readout std', True)
    gradient_std = _nonnegative(cal.get('gradient_readout_std_t_m'), 'gradient readout std', True)
    systematic = _nonnegative(cal.get('common_force_offset_std_n'), 'force systematic')
    sham_limit = _nonnegative(cal.get('coil_sham_max_abs_a'), 'sham-current threshold')
    active_min = _nonnegative(cal.get('coil_active_min_abs_a'), 'active-current threshold', True)
    if sham_limit >= active_min:
        raise ValueError('overlapping current thresholds')
    gap = cal.get('max_pair_gap_ns')
    if type(gap) is not int or not (0 < gap <= 10**13):
        raise ValueError('invalid time-window bound')
    try:
        text = stream_bytes.decode('utf-8')
    except UnicodeDecodeError as exc:
        raise ValueError('sensor stream not UTF-8') from exc
    reader = csv.DictReader(io.StringIO(text, newline=''), strict=True)
    if reader.fieldnames != list(COLUMNS):
        raise ValueError('unexpected or duplicate CSV columns')
    pairs = {}
    settings = []
    seen_settings = set()
    last_t = -1
    rows = 0
    for row in reader:
        rows += 1
        if rows > MAX_ROWS or None in row or any(v is None for v in row.values()):
            raise ValueError('missing/extra cells or excess rows')
        pid, sid = row['pair_id'], row['session_id']
        if not pid.strip() or not sid.strip() or len(pid) > 128 or len(sid) > 128:
            raise ValueError('missing or excessively long pair/session ID')
        condition = row['condition']
        if condition not in ('active', 'sham'):
            raise ValueError('invalid condition')
        ts = row['time_ns']
        if not ts.isascii() or not ts.isdecimal() or len(ts) > 20:
            raise ValueError('invalid integer timestamp')
        timestamp = int(ts)
        if timestamp <= last_t or timestamp >= 2**64:
            raise ValueError('timebase not strictly increasing')
        last_t = timestamp
        coil = _finite(row['coil_current_a'], 'coil current')
        if condition == 'active' and abs(coil) < active_min:
            raise ValueError('active row not measured above current threshold')
        if condition == 'sham' and abs(coil) > sham_limit:
            raise ValueError('sham exceeds off-current threshold')
        ds = row['dipole_sign']
        if ds not in ('-1', '1'):
            raise ValueError('missing or invalid dipole polarity')
        sign = int(ds)
        group = row['moment_calibration_id']
        moment = groups.get(group)
        if not isinstance(moment, dict):
            raise ValueError('unknown calibrated magnetic moment ID')
        m = _finite(moment.get('moment_am2'), 'moment')
        um = _nonnegative(moment.get('moment_std_am2'), 'moment std')
        if m == 0 or (1 if m > 0 else -1) != sign:
            raise ValueError('moment polarity contradicts calibrated moment')
        physical_magnet = moment.get('shared_magnitude_id')
        if not isinstance(physical_magnet, str) or not physical_magnet.strip():
            raise ValueError('physical shared-magnitude calibration ID required')
        force = _finite(row['force_n'], 'force')
        grad = _finite(row['gradient_t_m'], 'gradient')
        bin_sign = (1 if coil > 0 else -1) if condition == 'active' else 0
        arm = (bin_sign, sign)
        if arm not in seen_settings:
            settings.append({'coil_sign': arm[0], 'dipole_sign': arm[1]})
            seen_settings.add(arm)
        key = (pid, sid)
        by_condition = pairs.setdefault(key, {})
        if condition in by_condition:
            raise ValueError('duplicate pair condition')
        by_condition[condition] = (timestamp, force, grad, group, m, um, sign,
                                   physical_magnet)
    if not rows:
        raise ValueError('empty sensor stream')
    output = []
    for (pid, sid), conditions in sorted(pairs.items()):
        if set(conditions) != {'active', 'sham'}:
            raise ValueError('incomplete pair')
        a, s = conditions['active'], conditions['sham']
        if abs(a[0] - s[0]) > gap or a[3:] != s[3:]:
            raise ValueError('pair time or calibration identity mismatch')
        output.append({'pair_id':pid, 'session_id':sid,
                       'moment_calibration_id':a[3],
                       'moment_covariance_group_id':a[7], 'moment_am2':a[4],
                       'moment_std_am2':a[5],
                       'common_systematic_std_n':systematic,
                       'active':{'force_n':a[1], 'force_std_n':force_std,
                                 'gradient_t_m':a[2], 'gradient_std_t_m':gradient_std},
                       'sham':{'force_n':s[1], 'force_std_n':force_std,
                               'gradient_t_m':s[2], 'gradient_std_t_m':gradient_std}})
    if not output:
        raise ValueError('no completed pair')
    return {'pairs':output, 'factorial_settings':settings,
            'row_count':rows, 'reducer_version':VERSION,
            'instrument_origin_authenticated':False}
