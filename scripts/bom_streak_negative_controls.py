#!/usr/bin/env python3
"""Candidate exact-copy streak detector for one SHA-verified BOM snapshot.

Reuses bom_versioned_same_object_audit.snapshot for file/byte admission. Finds
strict contiguous exact-value streaks, not gaps or near matches. A candidate
is NOT a transcription verdict: station aliases, co-located gauges, seasonality,
precision and original paper records need independent review.
"""
from __future__ import annotations
import argparse
from collections import defaultdict, Counter
from datetime import date
from decimal import Decimal
from hashlib import sha256
import json
from pathlib import Path

ANCHOR = 4


def _groups(rows):
    groups = defaultdict(list)
    for (station, day, variable), cell in rows.items():
        value = cell['value']
        if value:
            groups[(station, variable)].append((date.fromisoformat(day).toordinal(), Decimal(value), cell['flag']))
    return {k: sorted(v) for k, v in groups.items()}


def _anchors(seq, var):
    for i in range(len(seq) - ANCHOR + 1):
        cut = seq[i:i+ANCHOR]
        if any(cut[j+1][0] - cut[j][0] != 1 for j in range(ANCHOR-1)):
            continue
        values = tuple(c[1] for c in cut)
        if var == 'rain':
            if sum(v > 0 for v in values) < 2:
                continue
        elif len(set(values)) < 2:
            continue
        yield i, values


def _maximal(a, b, i, j):
    """Extend a matching 4-day anchor to maximal exact contiguous days."""
    lo_i, lo_j = i, j
    while lo_i and lo_j and a[lo_i-1][0] == a[lo_i][0]-1 and b[lo_j-1][0] == b[lo_j][0]-1 and a[lo_i-1][1] == b[lo_j-1][1]:
        lo_i -= 1
        lo_j -= 1
    hi_i, hi_j = i+ANCHOR, j+ANCHOR
    while hi_i < len(a) and hi_j < len(b) and a[hi_i][0] == a[hi_i-1][0]+1 and b[hi_j][0] == b[hi_j-1][0]+1 and a[hi_i][1] == b[hi_j][1]:
        hi_i += 1
        hi_j += 1
    return lo_i, lo_j, hi_i-lo_i


def scan(rows, min_days=12, min_lag=14, max_bucket=128, max_candidates=100000):
    """Return bounded candidates; missingness breaks runs; no inference of causality."""
    if min_days < ANCHOR or min_lag < ANCHOR or max_bucket < 2 or max_candidates < 1:
        raise ValueError('invalid detection thresholds')
    groups = _groups(rows)
    within = []
    cross = []
    evaluated = 0
    skipped = 0
    seen = set()
    # Within-station: identical informative windows at different dates.
    for (station, variable), seq in sorted(groups.items()):
        idx = defaultdict(list)
        for i, signature in _anchors(seq, variable):
            idx[signature].append(i)
        for positions in idx.values():
            if len(positions) > max_bucket:
                skipped += 1
                continue
            for n, i in enumerate(positions):
                for j in positions[n+1:]:
                    lag = seq[j][0] - seq[i][0]
                    if lag < min_lag:
                        continue
                    evaluated += 1
                    if evaluated > max_candidates:
                        raise ValueError('candidate comparison budget exceeded; narrow input or raise explicit budget')
                    x, y, length = _maximal(seq, seq, i, j)
                    # Maximal duplicate blocks must be disjoint to prevent self-overlaps.
                    if length < min_days or seq[x+length-1][0] >= seq[y][0]:
                        continue
                    values = [seq[t][1] for t in range(x, x+length)]
                    if variable == 'rain' and sum(v > 0 for v in values) < 3:
                        continue
                    key = ('within', station, variable, seq[x][0], seq[y][0], length)
                    if key in seen:
                        continue
                    seen.add(key)
                    within.append({'kind': 'within_station', 'station': station, 'variable': variable,
                                   'left_start': date.fromordinal(seq[x][0]).isoformat(),
                                   'right_start': date.fromordinal(seq[y][0]).isoformat(),
                                   'days': length, 'offset_days': lag,
                                   'informative_nonzero_days': sum(v != 0 for v in values),
                                   'quality_flag_disagreements': sum(seq[x+t][2] != seq[y+t][2] for t in range(length)),
                                   'interpretation': 'candidate_exact_match_only'})
    # Cross-station: same-day exact sequences. IDs distinct; sites may be co-located.
    by_var = defaultdict(lambda: defaultdict(list))
    for (station, variable), seq in groups.items():
        for i, signature in _anchors(seq, variable):
            by_var[variable][(seq[i][0], signature)].append((station, i))
    for variable, idx in by_var.items():
        for positions in idx.values():
            if len(positions) > max_bucket:
                skipped += 1
                continue
            for n, (sta, i) in enumerate(positions):
                for stb, j in positions[n+1:]:
                    if sta == stb:
                        continue
                    a, b = groups[(sta, variable)], groups[(stb, variable)]
                    evaluated += 1
                    if evaluated > max_candidates:
                        raise ValueError('candidate comparison budget exceeded; narrow input or raise explicit budget')
                    x, y, length = _maximal(a, b, i, j)
                    if length < min_days:
                        continue
                    values = [a[t][1] for t in range(x, x+length)]
                    if variable == 'rain' and sum(v > 0 for v in values) < 3:
                        continue
                    ids = tuple(sorted((sta, stb)))
                    key = ('across', ids, variable, a[x][0], length)
                    if key in seen:
                        continue
                    seen.add(key)
                    cross.append({'kind': 'cross_station', 'stations': list(ids), 'variable': variable,
                                  'start': date.fromordinal(a[x][0]).isoformat(),
                                  'days': length, 'informative_nonzero_days': sum(v != 0 for v in values),
                                  'station_independence': 'NOT_VERIFIED',
                                  'interpretation': 'candidate_exact_match_only'})
    return {'within': sorted(within, key=lambda z: (z['station'], z['left_start'], z['right_start'])),
            'cross': sorted(cross, key=lambda z: (z['stations'], z['start'])),
            'comparison_count': evaluated, 'skipped_high_multiplicity_anchors': skipped}


def rotate_months(rows, seed):
    """Deterministic month-within-station permutation, preserving missing-day mask.

    Different year/month/station offsets break shared-copy alignments; this is
    a negative-control diagnostic, not an exact conditional null distribution.
    """
    groups = defaultdict(list)
    for (station, day, variable), cell in rows.items():
        if cell['value'] != '':
            groups[(station, variable, day[:7])].append((station, day, variable))
    result = {k: dict(v) for k, v in rows.items()}
    for (station, var, month), keys in groups.items():
        keys.sort(key=lambda x: x[1])
        if len(keys) < 2:
            continue
        raw = sha256(f'{seed}|{station}|{var}|{month}'.encode()).digest()
        shift = 1 + int.from_bytes(raw[:4], 'big') % (len(keys)-1)
        originals = [rows[k]['value'] for k in keys]
        for i, key in enumerate(keys):
            result[key]['value'] = originals[(i + shift) % len(keys)]
    return result


def audit(rows, min_days=12, controls=3):
    if controls < 0 or controls > 20:
        raise ValueError('controls must be between 0 and 20')
    observed = scan(rows, min_days=min_days)
    nulls = []
    for seed in range(controls):
        result = scan(rotate_months(rows, seed), min_days=min_days)
        nulls.append({'seed': seed, 'within': len(result['within']), 'cross': len(result['cross'])})
    offsets = Counter(c['offset_days'] for c in observed['within'])
    return {'schema': 'dashi.bom.exact_streak_candidates.v1',
            'detection_scope': 'contiguous_exact_matches_only',
            'observed': observed, 'control_counts': nulls,
            'repeated_offset_days': {str(k): v for k, v in sorted(offsets.items()) if v > 1},
            'missing_rows_are_not_zero': True,
            'paper_originals_checked': False,
            'station_independence_checked': False,
            'copy_direction_established': False,
            'statistical_fdr_established': False,
            'climate_effect_computed': False}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--manifest', type=Path, required=True)
    parser.add_argument('--version', choices=['before', 'after'], default='after')
    parser.add_argument('--min-days', type=int, default=12)
    parser.add_argument('--controls', type=int, default=3)
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    from bom_versioned_same_object_audit import snapshot
    manifest = json.loads(args.manifest.read_text(encoding='utf-8'))
    if manifest.get('schema') != 'dashi.bom.same_object_snapshot.v1':
        parser.error('manifest schema mismatch')
    rows = snapshot(manifest[args.version], args.manifest.parent)
    answer = audit(rows, min_days=args.min_days, controls=args.controls)
    answer['snapshot_sha256'] = manifest[args.version]['sha256']
    rendered = json.dumps(answer, indent=2, sort_keys=True) + '\n'
    if args.output:
        args.output.write_text(rendered, encoding='utf-8')
    else:
        print(rendered, end='')

if __name__ == '__main__':
    main()
