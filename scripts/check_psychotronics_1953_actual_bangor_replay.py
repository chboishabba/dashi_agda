#!/usr/bin/env python3
"""Source-bounded replay of user-supplied NOAA 1953 Bangor Global Hourly CSV.

Weather observations: NOAA/NCEI and original Bangor observers. Uploaded bytes:
user. Case-specific replay/interpretation: Johl Brown with ChatGPT assistance.
Source hash records the upload only; never implies publisher authentication.
"""
import argparse
import csv
import hashlib
import json
from collections import Counter
from datetime import datetime, timezone
from pathlib import Path
from zoneinfo import ZoneInfo

STATION = '72607114606'
TARGET = '1953-07-07T02:00:00'
RAIN = {'50','51','52','53','54','55','56','57','58','59','60','61','62','63','64','65','66','67','68','69','80','81','82','83','84','89','90','91','92','95','96','97','99'}
WEATHER = {'80':'slight rain showers','81':'moderate or heavy rain showers','17':'thunderstorm, no precipitation at observation','51':'continuous slight drizzle','45':'fog, sky invisible, unchanged','61':'continuous slight rain'}

def analyze(path):
    blob = path.read_bytes()
    reader = csv.DictReader(blob.decode('utf-8-sig').splitlines())
    if not reader.fieldnames or not {'STATION','DATE','SOURCE','MW1','MW2','AA1','SLP'}.issubset(reader.fieldnames):
        raise ValueError('required NOAA Global Hourly CSV columns absent')
    seen, counts, rain, totals, source = set(), Counter(), [], [], Counter()
    first, last = None, None
    for row in reader:
        if row['STATION'] != STATION:
            raise ValueError('wrong original station family')
        utc = datetime.fromisoformat(row['DATE'].replace('Z','+00:00'))
        if utc.tzinfo is not None and utc.utcoffset().total_seconds() != 0:
            raise ValueError('non-UTC NOAA timestamp')
        stamp = utc.strftime('%Y-%m-%dT%H:%M:%S')
        if stamp in seen:
            raise ValueError('duplicate hourly record')
        seen.add(stamp)
        first = stamp if first is None else min(first,stamp)
        last = stamp if last is None else max(last,stamp)
        if not ('1953-07-05' <= stamp[:10] <= '1953-07-09'):
            continue
        counts[stamp[:10]] += 1
        source[row['SOURCE']] += 1
        local = utc.replace(tzinfo=timezone.utc).astimezone(ZoneInfo('America/New_York')).isoformat()
        for field in ('MW1','MW2','MW3','MW4'):
            value = row.get(field,'')
            if not value:
                continue
            pair=value.split(',')
            if len(pair)!=2:
                raise ValueError('bad NOAA manual weather tuple')
            if pair[0] in RAIN:
                rain.append({'utc':stamp+'Z','local':local,'field':field,'weather_code':pair[0],'quality':pair[1],'meaning':WEATHER.get(pair[0],'precipitation weather code')})
        aa = row.get('AA1','')
        if aa:
            group=aa.split(',')
            if len(group)!=4 or not group[0].isdigit() or not group[1].isdigit():
                raise ValueError('bad NOAA 24-hour precipitation tuple')
            totals.append({'utc':stamp+'Z','local':local,'AA1_raw':aa,'hours':int(group[0]),'mm':int(group[1])/10,'condition_code':group[2],'quality_code':group[3]})
    if not seen:
        raise ValueError('empty input')
    observed = next((r for r in rain if r['utc']==TARGET+'Z' and r['field']=='MW1' and r['weather_code']=='80'),None)
    return {'upload_sha256':hashlib.sha256(blob).hexdigest(),'input_bytes':len(blob),
            'rows':len(seen),'first_utc':first+'Z','last_utc':last+'Z',
            'station':STATION,'window_utc_counts':dict(sorted(counts.items())),
            'source_counts':dict(sorted(source.items())),
            'weather_at_1953_07_06_2200_local':observed,
            'first_rain_weather_in_window':min(rain,key=lambda x:x['utc']) if rain else None,
            'rain_weather_rows':rain,'24h_precipitation_reports':totals,
            'limits':{'uploaded_original_publisher_SHA_authenticated':False,
                      'same_location_as_Ellsworth':False,
                      'exact_rain_onset_determined':False,
                      'AA1_24h_amount_equals_hourly_rain':False,
                      'multiple_NOAA_formats_independent_replications':False,
                      'cloudbuster_causality_supported':False}}

def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--csv',required=True,type=Path)
    parser.add_argument('--json-out',type=Path)
    args=parser.parse_args()
    result=analyze(args.csv)
    encoded=json.dumps(result,indent=2,sort_keys=True)+'\n'
    if args.json_out:
        args.json_out.write_text(encoded,encoding='utf8')
    else:
        print(encoded,end='')

if __name__=='__main__':
    main()
