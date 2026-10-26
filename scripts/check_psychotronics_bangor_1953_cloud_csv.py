#!/usr/bin/env python3
"""NOAA Global Hourly 1953 Bangor converted CSV: original-custody-limited reader.

Original weather observations and conversion belong to NOAA/NCEI and its
historical observers. This case-specific decoder is by Johl Brown with
OpenAI ChatGPT assistance. A converted CSV is NOT a second instrument.
The year directory is user-visible, but this station's exact CSV KEY and
actual July rows are not verified until listing/file data are acquired.
"""
from __future__ import annotations

import argparse
import csv
import hashlib
import io
import json
import urllib.error
import urllib.parse
import urllib.request
from collections import Counter
from datetime import datetime, timezone
from pathlib import Path

from locate_psychotronics_noaa_isd_1953_s3 import parse_listing

BUCKET = 'https://noaa-global-hourly-pds.s3.amazonaws.com'
STATION = '72607114606'  # original ISD USAF 726071 + WBAN 14606; candidate CSV name
BASENAME = STATION + '.csv'
CONFIRMED_YEAR_DIRECTORY = '1953/'  # user-provided first-party Explorer view
TARGET_PREFIX = CONFIRMED_YEAR_DIRECTORY + STATION
START, END = '1953-07-05', '1953-07-09'
MAX_PAGES = 8
TIMEOUT = 15


def list_station_key(fetch=None):
    """Resolve actual CSV S3 key via list reply, not derived filename alone."""
    if fetch is None:
        fetch = urllib.request.urlopen
    scans, matches, errors = [], [], []
    token, visited = None, set()
    for i in range(MAX_PAGES):
        params = {'list-type': '2', 'prefix': TARGET_PREFIX}
        if token is not None:
            params['continuation-token'] = token
        url = BUCKET + '/?' + urllib.parse.urlencode(params)
        try:
            with fetch(url, timeout=TIMEOUT) as r:
                objects, next_token = parse_listing(r.read())
        except (OSError, urllib.error.URLError, ValueError) as e:
            errors.append(str(e)[:250])
            break
        scans.append({'page': i, 'listed': len(objects), 'prefix': TARGET_PREFIX})
        for obj in objects:
            if obj['key'] == CONFIRMED_YEAR_DIRECTORY + BASENAME:
                matches.append(obj)
        if next_token is None:
            break
        if next_token in visited:
            errors.append('S3 continuation token repeated')
            break
        visited.add(next_token)
        token = next_token
    else:
        errors.append('bounded listing page budget exhausted')
    return {
        'original_agency': 'NOAA/NCEI ISD Global Hourly',
        'NOAA_csv_bucket': BUCKET,
        'confirmed_by_user_1953_directory': CONFIRMED_YEAR_DIRECTORY,
        'candidate_station_csv_name_not_preverified': BASENAME,
        'actual_listed_matches': matches,
        'listing_scans': scans,
        'listing_errors': errors,
        'hourly_observations_acquired': False,
        'same_source_as_original_ISD_possible': True,
    }


def inspect_csv_text(text):
    """Read UTC labels and raw quality groups; no precipitation interpretation."""
    reader = csv.DictReader(io.StringIO(text))
    if not reader.fieldnames or not {'STATION', 'DATE'}.issubset(reader.fieldnames):
        raise ValueError('missing original converted NOAA STATION/DATE columns')
    counts = Counter()
    times, aa, sources = {}, {}, Counter()
    n = 0
    for row in reader:
        n += 1
        if row.get('STATION', '') != STATION:
            raise ValueError('converted CSV station ID does not match historic Bangor source family')
        raw = row.get('DATE', '')
        if not raw:
            raise ValueError('missing UTC DATE')
        try:
            timestamp = datetime.fromisoformat(raw.replace('Z', '+00:00'))
        except ValueError as exc:
            raise ValueError('invalid NOAA converted CSV timestamp') from exc
        if timestamp.tzinfo is not None and timestamp.utcoffset().total_seconds() != 0:
            raise ValueError('non-UTC timezone in NOAA UTC timestamp')
        day = timestamp.strftime('%Y-%m-%d')
        if START <= day <= END:
            counts[day] += 1
            times.setdefault(day, []).append(timestamp.strftime('%H:%M:%S'))
            sources[row.get('SOURCE', '')] += 1
            # OPAQUE encoded NOAA precipitation and present weather values.
            # The AA codes describe accumulation periods, not event onset.
            aa.setdefault(day, []).append({
                'utc': timestamp.strftime('%H:%M:%S'),
                'AA1_uninterpreted': row.get('AA1', ''),
                'MW1_uninterpreted': row.get('MW1', ''),
                'quality_control_uninterpreted': row.get('QUALITY_CONTROL', ''),
            })
    if not n or not counts:
        raise ValueError('no 5-9 July 1953 converted NOAA Bangor observations')
    return {
        'rows_all_dates': n,
        'utc_observation_counts_by_date': dict(sorted(counts.items())),
        'utc_labels_within_window': {k: sorted(v) for k, v in sorted(times.items())},
        'source_code_counts_without_independence_inference': dict(sorted(sources.items())),
        'encoded_rain_and_weather_groups_not_interpreted': aa,
        'rainfall_onset_hour_identified': False,
        'original_1953_at_site_Ellsworth_observation': False,
        'Reich_causality_established': False,
    }


def inspect_file(path):
    blob = path.read_bytes()
    if len(blob) > 25_000_000:
        raise ValueError('excessively large unexpected station CSV input')
    text = blob.decode('utf-8-sig')
    out = inspect_csv_text(text)
    out['local_file_sha256_no_publisher_byte_attestation'] = hashlib.sha256(blob).hexdigest()
    out['csv_original_publisher_custody_verified'] = False
    return out


def acquire_from_actual_listing(result, path, fetch=None):
    """Fetch converted CSV only when original S3 LIST gave exact unique key."""
    matches = result['actual_listed_matches']
    if len(matches) != 1 or matches[0]['key'] != CONFIRMED_YEAR_DIRECTORY + BASENAME:
        raise ValueError('exact original station-year CSV S3 key not uniquely observed')
    if path.exists():
        raise FileExistsError('never overwrite a previously acquired source')
    if fetch is None:
        fetch = urllib.request.urlopen
    key = matches[0]['key']
    url = BUCKET + '/' + urllib.parse.quote(key, safe='/')
    with fetch(url, timeout=TIMEOUT) as response:
        blob = response.read()
    if len(blob) > 25_000_000:
        raise ValueError('unexpected oversized station CSV')
    sample = inspect_csv_text(blob.decode('utf-8-sig'))
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_bytes(blob)
    return {
        'url_from_actual_listed_key': url,
        'saved_path': str(path),
        'local_sha256_not_agency_authenticated': hashlib.sha256(blob).hexdigest(),
        'original_fixed_width_ISD_format': False,
        'derived_converted_csv': True,
        'original_1953_precipitation_hour_interpreted': False,
        'checked_utc_obs_count': sample['utc_observation_counts_by_date'],
    }


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--csv', type=Path, help='read already-acquired original NOAA-converted CSV')
    p.add_argument('--list-actual', action='store_true')
    p.add_argument('--download-to', type=Path)
    a = p.parse_args()
    if not (a.csv or a.list_actual or a.download_to):
        p.error('choose --csv, --list-actual or --download-to')
    out = {}
    if a.csv:
        out['local_csv_read'] = inspect_file(a.csv)
    if a.list_actual or a.download_to:
        out['s3'] = list_station_key()
        if a.download_to:
            out['download'] = acquire_from_actual_listing(out['s3'], a.download_to)
    print(json.dumps(out, indent=2, sort_keys=True))


if __name__ == '__main__':
    main()
