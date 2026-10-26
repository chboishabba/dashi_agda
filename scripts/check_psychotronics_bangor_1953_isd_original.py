#!/usr/bin/env python3
"""Fail-closed source-original ISD 1953 Bangor observation *time* inventory.

NOAA/NCEI owns the original ISD data and 1953 station-year archive;
Johl Brown with OpenAI ChatGPT assistance owns only this adaptation.
File listing is VERIFIED; archive data bytes are NOT yet authenticated.
These timestamps are UTC observation labels, NOT rain onset or causation.
"""
import argparse
import gzip
import hashlib
import json
from collections import Counter
from pathlib import Path

FILE_NAME = '726071-14606-1953.gz'
ORIGINAL = 'https://www.ncei.noaa.gov/pub/data/noaa/1953/' + FILE_NAME
USAF, WBAN = '726071', '14606'
START, END = '19530705', '19530709'


def parse_header(line):
    record = line.rstrip('\r\n')
    if len(record) < 105 or not record[:4].isascii() or not record[:4].isdigit():
        raise ValueError('invalid ISD record length/mandatory section')
    declared = int(record[:4])
    if len(record) != declared:
        raise ValueError(f'ISD declared record length mismatch: {declared} != {len(record)}')
    if (record[4:10], record[10:15]) != (USAF, WBAN):
        raise ValueError('wrong ISD USAF/WBAN station')
    date, time = record[15:23], record[23:27]
    if (len(date) != 8 or not date.isascii() or not date.isdigit() or
            len(time) != 4 or not time.isascii() or not time.isdigit()):
        raise ValueError('invalid ISD timestamp')
    hr, minute = int(time[:2]), int(time[2:])
    if hr > 23 or minute > 59:
        raise ValueError('invalid ISD clock')
    return {'utc_date': date, 'utc_time': time, 'source_flag': record[27]}


def examine(path):
    opener = gzip.open if path.suffix == '.gz' else open
    hashes = hashlib.sha256(path.read_bytes()).hexdigest()
    by_day = Counter()
    times = {}
    physical_rows = 0
    with opener(path, 'rt', encoding='ascii', newline='') as stream:
        for line in stream:
            physical_rows += 1
            row = parse_header(line)
            if START <= row['utc_date'] <= END:
                day = row['utc_date']
                by_day[day] += 1
                times.setdefault(day, []).append(row['utc_time'])
    if not physical_rows:
        raise ValueError('empty original-format ISD input')
    if not by_day:
        raise ValueError('no UTC observations in 1953-07-05 through 1953-07-09')
    return {
        'local_input_sha256': hashes,
        'local_input_parsed_not_noaa_authenticated': True,
        'original_noaa_full_file_bytes_authenticated': False,
        'original_archive_locator': ORIGINAL,
        'station_ids': {'usaf': USAF, 'wban': WBAN},
        'utc_hourly_or_synoptic_observation_counts': dict(sorted(by_day.items())),
        'utc_time_labels': {d: sorted(v) for d, v in sorted(times.items())},
        'historical_ellsworth_rain_onset_verified': False,
        'precipitation_payload_interpreted': False,
        'local_timezone_alignment_verified': False,
        'causal_intervention_verified': False,
    }


def synthetic_record(date='19530706', time='1200', usaf=USAF, wban=WBAN):
    # Mimics fixed-width control/mandatory length; not actual NOAA data.
    content = '0000' + usaf + wban + date + time + '4' + ('9' * 77)
    assert len(content) == 105
    return f'{len(content):04d}' + content[4:]


def self_test():
    import tempfile
    sample = synthetic_record()
    assert parse_header(sample)['utc_time'] == '1200'
    cases = 0
    for bad in (sample[:-1], synthetic_record(time='2460'),
                synthetic_record(wban='99999'), synthetic_record(date='195307AA'),
                'x' + sample[1:]):
        try:
            parse_header(bad)
        except ValueError:
            cases += 1
        else:
            raise AssertionError('synthetic corrupt ISD record accepted')
    with tempfile.TemporaryDirectory() as d:
        p = Path(d) / FILE_NAME
        with gzip.open(p, 'wt', encoding='ascii') as out:
            out.write(synthetic_record('19530706', '0100') + '\n')
            out.write(synthetic_record('19530706', '2300') + '\n')
            out.write(synthetic_record('19530707', '0030') + '\n')
        result = examine(p)
        assert result['utc_hourly_or_synoptic_observation_counts'] == {'19530706': 2, '19530707': 1}
        assert result['precipitation_payload_interpreted'] is False
    return {'synthetic_negative_cases_passed': cases, 'gzip_scan_passed': True,
            'publisher_1953_original_bytes_acquired': False}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--original-isd', type=Path)
    parser.add_argument('--self-test', action='store_true')
    args = parser.parse_args()
    result = {'NOAA_original_archive_listing': ORIGINAL,
              'archive_year_object_exists': True,
              'actual_1953_file_opened': args.original_isd is not None}
    if args.original_isd:
        result['local_analysis'] = examine(args.original_isd)
    if args.self_test:
        result['self_test'] = self_test()
    print(json.dumps(result, indent=2, sort_keys=True))

if __name__ == '__main__':
    main()
