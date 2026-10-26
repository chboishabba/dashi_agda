#!/usr/bin/env python3
"""Fail-closed real Bangor 1953 ISD/NOAA Global Hourly synoptic-nuisance audit.

Original observations: 1953 Bangor USAF observers and NOAA/NCEI archival conversion.
Original account: Wilhelm Reich (1954) and July 8 Ellsworth American reporting.
Case-specific source-typed computational analysis: Johl Brown with ChatGPT help.
No source identity, map-scale weather-system, rain-onset, or causal equivalence.
"""
import argparse
import csv
import hashlib
import json
from datetime import datetime, timedelta, timezone
from pathlib import Path
from zoneinfo import ZoneInfo

STATION = '72607114606'
EXPECTED_SHA256 = '2a3b048d620b320fb8d1cf548d4eb06fb2c49821faa54c4cc7f708649cdca9bd'
OP_START = '1953-07-06T14:45:00'  # documented 10:45 EDT Graham Lake
OP_END = '1953-07-06T15:52:00'  # documented 11:52 EDT Graham Lake
FIRST_RAIN_OBS = '1953-07-07T02:00:00'  # hourly MW1=80 at Bangor, not first drop
OBS_TIMES = ('1953-07-06T02:00:00', '1953-07-06T12:00:00',
             '1953-07-06T14:00:00', '1953-07-06T15:00:00',
             '1953-07-06T16:00:00', '1953-07-06T18:00:00',
             '1953-07-06T20:00:00', '1953-07-07T00:00:00',
             '1953-07-07T02:00:00', '1953-07-07T04:00:00',
             '1953-07-07T05:00:00', '1953-07-07T08:00:00')


def quality_pair(s, *, sentinel, divisor, accepted=('1',)):
    """Interpret a genuine NOAA code/value pair only when QC and not missing."""
    if not s:
        return None
    fields = s.split(',')
    if len(fields) != 2:
        raise ValueError('malformed two-part original NOAA field')
    value, qc = fields
    if value in (sentinel, '-' + sentinel, '+' + sentinel):
        return None
    if not value.lstrip('+-').isdigit():
        raise ValueError('nonnumeric original NOAA field')
    if qc not in accepted:
        return None
    return int(value) / divisor


def wind_field(s):
    parts = s.split(',')
    if len(parts) != 5:
        raise ValueError('invalid original NOAA WND tuple')
    raw_dir, dir_qc, kind, raw_speed, speed_qc = parts
    direction = None if raw_dir == '999' or dir_qc != '1' else int(raw_dir)
    speed = None if raw_speed == '9999' or speed_qc != '1' else int(raw_speed) / 10
    return {'direction_from_true_north_deg': direction,
            'speed_mps': speed, 'type': kind,
            'direction_quality': dir_qc, 'speed_quality': speed_qc}


def ceiling_field(s):
    if not s:
        return None
    fields=s.split(',')
    if len(fields) != 4:
        raise ValueError('bad NOAA CIG tuple')
    raw, qc = fields[0], fields[1]
    if qc != '1' or raw == '99999':
        return None
    if raw == '22000':
        return {'metres_agl': None, 'unlimited_reported': True, 'quality': qc}
    return {'metres_agl': int(raw), 'unlimited_reported': False, 'quality': qc}


def analyze_csv(path, *, require_original_upload_digest=True):
    blob=Path(path).read_bytes()
    digest=hashlib.sha256(blob).hexdigest()
    if require_original_upload_digest and digest != EXPECTED_SHA256:
        raise ValueError('local input bytes differ from original user-supplied verified dataset')
    rows={}
    reader=csv.DictReader(blob.decode('utf-8-sig').splitlines())
    required={'STATION','DATE','SLP','WND','CIG','MW1','SOURCE','QUALITY_CONTROL'}
    if not reader.fieldnames or not required.issubset(reader.fieldnames):
        raise ValueError('missing required NOAA Global Hourly columns')
    for r in reader:
        if r['STATION'] != STATION:
            raise ValueError('wrong station; this audit is exactly Bangor only')
        t=datetime.fromisoformat(r['DATE'].replace('Z','+00:00'))
        if t.tzinfo and t.utcoffset() != timedelta(0):
            raise ValueError('observation is not UTC')
        key=t.replace(tzinfo=None).isoformat(timespec='seconds')
        if key in rows:
            raise ValueError('duplicate original hourly timestamp')
        rows[key]=r
    if FIRST_RAIN_OBS not in rows or any(t not in rows for t in OBS_TIMES):
        raise ValueError('target hourly observation missing')
    witness=rows[FIRST_RAIN_OBS]
    if witness['MW1'] != '80,1':
        raise ValueError('reported first target shower lacks NOAA original QC code 80,1')
    window=[]
    for key in OBS_TIMES:
        r=rows[key]
        p=quality_pair(r['SLP'], sentinel='99999', divisor=10)
        wind=wind_field(r['WND'])
        local=datetime.fromisoformat(key).replace(tzinfo=timezone.utc).astimezone(ZoneInfo('America/New_York'))
        window.append({'utc':key+'Z','local_EDT':local.isoformat(),
                       'sea_level_pressure_hpa':p,'pressure_quality_code':r['SLP'].split(',')[1],
                       'wind':wind,'ceiling':ceiling_field(r['CIG']),
                       'manual_weather_code':r['MW1'], 'source':r['SOURCE']})
    def tenths(t):
        val=quality_pair(rows[t]['SLP'], sentinel='99999', divisor=1)
        return int(val) if val is not None else None
    def delta(a,b):
        x,y=tenths(a),tenths(b)
        if x is None or y is None:
            raise ValueError('selected pressure delta missing original QC-passing component')
        return (y-x)/10
    drops={str(hours)+'h_before_observed_02Z_shower':delta(
        (datetime.fromisoformat(FIRST_RAIN_OBS)-timedelta(hours=hours)).isoformat(timespec='seconds'),FIRST_RAIN_OBS)
        for hours in (6,12,24)}
    july_12=[]
    for end in sorted(rows):
        if not end.startswith('1953-07-'): continue
        start=(datetime.fromisoformat(end)-timedelta(hours=12)).isoformat(timespec='seconds')
        if start not in rows:continue
        p0,p1=tenths(start),tenths(end)
        if p0 is not None and p1 is not None:
            july_12.append((p1-p0)/10)
    target=drops['12h_before_observed_02Z_shower']
    n=len(july_12);extreme=sum(x<=target for x in july_12)
    if n==0:
        raise ValueError('no quality-passing historical July control windows')
    start_local=datetime.fromisoformat(OP_START).replace(tzinfo=timezone.utc).astimezone(ZoneInfo('America/New_York'))
    end_local=datetime.fromisoformat(OP_END).replace(tzinfo=timezone.utc).astimezone(ZoneInfo('America/New_York'))
    return {
        'original_file':Path(path).name, 'local_sha256_not_noaa_publisher_authenticated':digest,
        'station':STATION, 'original_observation_hours':len(rows),
        'source_and_reporting_custody':'USAF hourly data compiled by NOAA/NCEI, not new experiment',
        'documented_operation_Graham_Lake':{'utc_start':OP_START+'Z','utc_end':OP_END+'Z',
                                            'local_start':start_local.isoformat(), 'local_end':end_local.isoformat(),
                                            'author_root':'Reich 1954 / Ellsworth American 1953 separate written claims'},
        'fixed_hourly_pressure_and_wind':window,
        'quality_passing_pressure_deltas_hpa':drops,
        'july_1953_end_in_july_12h_pressure_control_windows':{
            'eligible_overlapping_hour_pairs':n, 'pairs_with_drop_at_least_as_large_as_event':extreme,
            'descriptive_fraction_not_causal_probability':extreme/n,
            'independent_samples_or_permutation_p_value':False,
            'note':'Every July endpoint compared to 12h prior; nested serially overlapping windows, includes wet/dry hours, no randomized controls.'},
        'wind_at_bangor_during_UTC14_to16':[wind_field(rows['1953-07-06T%02d:00:00'%h]['WND']) for h in (14,15,16)],
        'limitations':{
            'original_noaa_remote_upload_hash_authenticated':False,
            'pressure_drop_proves_specific_synoptic_front':False,
            'wind_at_bangor_same_as_Graham_Lake':False,
            'rain_at_observation_proves_exact_onset':False,
            'barometric_change_is_proof_for_or_against_cloudbuster':False,
            'regional_same_time_correlation_is_device_causal_effect':False,
            '1953_daily_weather_map_original_page_examined':False}}


def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--csv',required=True,type=Path)
    p.add_argument('--allow-unverified-input-for-fixture-only',action='store_true')
    p.add_argument('--json-out',type=Path)
    a=p.parse_args()
    result=analyze_csv(a.csv,require_original_upload_digest=not a.allow_unverified_input_for_fixture_only)
    raw=json.dumps(result,indent=2,sort_keys=True)+'\n'
    if a.json_out:
        if a.json_out.exists():
            raise FileExistsError('refuse to overwrite original receipt')
        a.json_out.write_text(raw,encoding='utf-8')
    else:
        print(raw,end='')

if __name__=='__main__':
    main()
