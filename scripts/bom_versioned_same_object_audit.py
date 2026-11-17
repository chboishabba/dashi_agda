#!/usr/bin/env python3
"""Fail-closed, source-hashed BOM snapshot comparison; not an anomaly verdict.

Input manifest JSON has `before` and `after` entries, each containing
`file`, `sha256`, `source_url`, and timezone-aware `captured_utc`.
Each CSV contains station_id,date,variable,value,flag. Permitted variables:
tmax, tmin, rain. Empty value means explicitly missing; absent key means no row.
The program cannot authenticate the publisher, reconstruct original paper
records, infer copying/intent, or estimate ACORN-SAT climate trends.
"""
from __future__ import annotations
import argparse
import csv
from datetime import date, datetime
from decimal import Decimal, InvalidOperation
from hashlib import sha256
import io
import json
from pathlib import Path
from urllib.parse import urlparse

FIELDS = ('station_id', 'date', 'variable', 'value', 'flag')
VARIABLES = {'tmax', 'tmin', 'rain'}

class AuditError(ValueError):
    pass

def insist(condition, message):
    if not condition:
        raise AuditError(message)

def snapshot(spec, root):
    insist(isinstance(spec, dict), 'snapshot must be an object')
    insist(all(isinstance(spec.get(k), str) and spec[k] for k in
               ('file', 'sha256', 'source_url', 'captured_utc')),
           'snapshot requires file, sha256, source_url, captured_utc')
    rel = Path(spec['file'])
    insist(not rel.is_absolute(), 'snapshot file must be relative to manifest')
    path = (root / rel).resolve()
    insist(path.is_relative_to(root.resolve()), 'snapshot file escapes manifest directory')
    insist(len(spec['sha256']) == 64 and all(c in '0123456789abcdef' for c in spec['sha256']),
           'sha256 must be 64 lower-case hexadecimal characters')
    url = urlparse(spec['source_url'])
    insist(url.scheme == 'https' and bool(url.hostname), 'source_url must be HTTPS')
    try:
        timestamp = datetime.fromisoformat(spec['captured_utc'].replace('Z', '+00:00'))
    except ValueError as ex:
        raise AuditError('invalid captured_utc') from ex
    insist(timestamp.tzinfo is not None and timestamp.utcoffset() is not None,
           'captured_utc needs a timezone offset')
    raw = path.read_bytes()
    actual = sha256(raw).hexdigest()
    insist(actual == spec['sha256'], f'bytes/hash mismatch: {rel}')
    try:
        source = io.StringIO(raw.decode('utf-8-sig'), newline='')
    except UnicodeDecodeError as ex:
        raise AuditError('invalid UTF-8 input') from ex
    reader = csv.DictReader(source)
    insist(tuple(reader.fieldnames or ()) == FIELDS, 'unexpected CSV header')
    rows = {}
    for line, row in enumerate(reader, 2):
        insist(None not in row and all(v is not None for v in row.values()),
               f'CSV shape error at line {line}')
        station, day, variable, value, flag = [row[k].strip() for k in FIELDS]
        insist(bool(station), f'empty station at {line}')
        insist(variable in VARIABLES, f'unknown variable at {line}')
        try:
            insist(date.fromisoformat(day).isoformat() == day, 'noncanonical ISO date')
        except ValueError as ex:
            raise AuditError(f'invalid date at {line}') from ex
        if value != '':
            try:
                number = Decimal(value)
                insist(number.is_finite(), f'nonfinite observation at {line}')
            except InvalidOperation as ex:
                raise AuditError(f'invalid observation at {line}') from ex
        key = (station, day, variable)
        insist(key not in rows, f'duplicate station/date/variable at line {line}: {key}')
        rows[key] = {'value': value, 'flag': flag}
    return rows

def classify(old, new):
    if old is None:
        return 'row_added'
    if new is None:
        return 'row_removed'
    a, b = old['value'], new['value']
    if a != b:
        if a == '':
            return 'value_added'
        if b == '':
            return 'value_removed'
        if Decimal(a) == Decimal(b):
            return 'numeric_format_changed'
        return 'value_changed'
    if old['flag'] != new['flag']:
        return 'flag_changed'
    return None

def audit(manifest, root):
    insist(manifest.get('schema') == 'dashi.bom.same_object_snapshot.v1', 'unknown schema')
    a, b = manifest.get('before'), manifest.get('after')
    insist(isinstance(a, dict) and isinstance(b, dict), 'two snapshots required')
    insist(a['sha256'] != b['sha256'], 'same bytes supplied for both snapshots')
    first, last = snapshot(a, root), snapshot(b, root)
    events = []
    counts = {}
    for station, day, variable in sorted(first.keys() | last.keys()):
        old, new = first.get((station, day, variable)), last.get((station, day, variable))
        category = classify(old, new)
        if category:
            counts[category] = counts.get(category, 0) + 1
            events.append({'station_id': station, 'date': day, 'variable': variable,
                           'change': category, 'before': old, 'after': new})
    return {'schema': 'dashi.bom.same_object_diff.v1',
            'before_sha256': a['sha256'], 'after_sha256': b['sha256'],
            'before_rows': len(first), 'after_rows': len(last),
            'counts': counts, 'events': events,
            'source_authenticity_verified': False,
            'archival_originals_compared': False,
            'climate_trend_effect_computed': False,
            'intent_or_coordination_inferred': False}

def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--manifest', type=Path, required=True)
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    try:
        manifest = json.loads(args.manifest.read_text(encoding='utf-8'))
        result = audit(manifest, args.manifest.parent)
    except (AuditError, OSError, KeyError, json.JSONDecodeError) as ex:
        parser.error(str(ex))
    rendered = json.dumps(result, indent=2, sort_keys=True) + '\n'
    if args.output:
        args.output.write_text(rendered, encoding='utf-8')
    else:
        print(rendered, end='')

if __name__ == '__main__':
    main()
