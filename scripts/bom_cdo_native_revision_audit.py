#!/usr/bin/env python3
"""Compare archived native BOM CDO CSVs; never derive counts from prose.

Manifest: {"schema":"dashi.bom.cdo.native_revision.v1",
 "before":[{"path":"file.csv","sha256":"...","capture_utc":"2026-05-01T00:00:00+10:00"}],
 "after":[{"path":"file.csv","sha256":"...","capture_utc":"2026-10-30T00:00:00+10:00"}]}
This program does not download or authenticate historical publisher identity.
"""
from __future__ import annotations
import argparse
from collections import Counter
import csv
from datetime import date, datetime
from decimal import Decimal, InvalidOperation
from hashlib import sha256
import io, json
from pathlib import Path

PRODUCTS = {
 'IDCJAC0010': ('tmax', 'Maximum temperature (Degree C)', 'Days of accumulation of maximum temperature'),
 'IDCJAC0011': ('tmin', 'Minimum temperature (Degree C)', 'Days of accumulation of minimum temperature'),
 'IDCJAC0009': ('rain', 'Rainfall amount (millimetres)', 'Period over which rainfall was measured (days)'),
}
BASE = ['Product code','Bureau of Meteorology station number','Year','Month','Day']

class AuditError(ValueError): pass

def check(condition, msg):
    if not condition: raise AuditError(msg)

def canon_num(x, *, empty_ok=True):
    x=x.strip()
    if not x:
        check(empty_ok, 'required number missing')
        return None
    try: d=Decimal(x)
    except InvalidOperation as e: raise AuditError('invalid number '+repr(x)) from e
    check(d.is_finite(), 'nonfinite numeric token')
    return d

def _time(s):
    try: dt=datetime.fromisoformat(s.replace('Z','+00:00'))
    except (ValueError, AttributeError) as e: raise AuditError('invalid capture_utc') from e
    check(dt.tzinfo is not None and dt.utcoffset() is not None, 'capture_utc needs offset')
    return dt

def read_set(specs, root):
    check(isinstance(specs,list) and specs, 'nonempty snapshot files required')
    rows={}; receipts=[]
    for spec in specs:
        check(isinstance(spec,dict), 'invalid file receipt')
        path=spec.get('path'); digest=spec.get('sha256'); when=spec.get('capture_utc')
        check(isinstance(path,str) and path and isinstance(digest,str) and len(digest)==64,
              'file path/hash receipt required')
        check(all(c in '0123456789abcdef' for c in digest), 'sha256 must be lowercase hex')
        dt=_time(when)
        rel=Path(path)
        check(not rel.is_absolute(), 'absolute paths refused')
        target=(root/rel).resolve()
        check(target.is_relative_to(root.resolve()), 'file outside archive root')
        buf=target.read_bytes()
        check(sha256(buf).hexdigest()==digest,'SHA256 mismatch: '+path)
        try: parsed=csv.DictReader(io.StringIO(buf.decode('utf-8-sig'),newline=''))
        except UnicodeDecodeError as e: raise AuditError('not UTF8: '+path) from e
        headers=parsed.fieldnames or []
        check(all(k in headers for k in BASE), 'BOM CDO base headers missing: '+path)
        check('Quality' in headers, 'quality header missing: '+path)
        n=0
        for lineno,line in enumerate(parsed,2):
            check(None not in line and all(v is not None for v in line.values()),
                  f'CSV malformed {path}:{lineno}')
            product=line['Product code'].strip()
            check(product in PRODUCTS,'unexpected product '+product)
            variable,value_col,days_col=PRODUCTS[product]
            check(value_col in headers and days_col in headers, 'BOM CDO product-specific fields missing')
            sid=line['Bureau of Meteorology station number'].strip()
            check(sid.isdecimal() and len(sid)<=6, 'bad station ID')
            station=sid.zfill(6)
            try:
                y,m,d=(int(line[c].strip()) for c in ('Year','Month','Day'))
                day=date(y,m,d).isoformat()
            except (ValueError,OverflowError) as e: raise AuditError(f'bad date at {path}:{lineno}') from e
            val=canon_num(line[value_col]); accum=canon_num(line[days_col])
            if accum is not None:
                check(accum>0 and accum==accum.to_integral_value(), 'invalid accumulation days')
            quality=line['Quality'].strip()
            key=(station,day,variable)
            check(key not in rows,f'duplicate station/day/product at {path}:{lineno}: {key}')
            rows[key]=(val,accum,quality)
            n+=1
        receipts.append({'path':path,'sha256':digest,'capture_utc':dt.isoformat(),'rows':n})
    return rows,receipts

def audit(manifest,root):
    check(manifest.get('schema')=='dashi.bom.cdo.native_revision.v1', 'invalid manifest schema')
    before,old=read_set(manifest.get('before'),root)
    after,new=read_set(manifest.get('after'),root)
    old_times=[datetime.fromisoformat(x['capture_utc']) for x in old]
    new_times=[datetime.fromisoformat(x['capture_utc']) for x in new]
    check(max(old_times)<min(new_times), 'time order overlaps or reverses')
    old_sets={(s,v) for s,_,v in before}; new_sets={(s,v) for s,_,v in after}
    overlap=old_sets&new_sets
    check(bool(overlap), 'no paired station/product files')
    unpaired=sorted(old_sets ^ new_sets)
    check(not unpaired, 'unpaired station/product archive: '+repr(unpaired[:10]))
    counts=Counter(); removals=Counter(); lost_values=Counter(); events=[]
    for station,day,var in sorted(set(before)|set(after)):
        oldrow=before.get((station,day,var));newrow=after.get((station,day,var))
        if oldrow is None or newrow is None:
            kind='calendar_row_added' if oldrow is None else 'calendar_row_removed'
        else:
            x,y=oldrow[0],newrow[0]
            if x is not None and y is None: kind='value_removed'
            elif x is None and y is not None: kind='value_added'
            elif x is not None and y is not None and x!=y: kind='value_changed'
            elif oldrow[1]!=newrow[1]: kind='accumulation_changed'
            elif oldrow[2]!=newrow[2]: kind='quality_flag_changed'
            else: continue
        counts[kind]+=1
        if kind=='value_removed':removals[(station,var)]+=1
        # A removed calendar row may contain a lost observation. Preserve
        # both the structural row change and the measured-data loss.
        if (oldrow is not None and oldrow[0] is not None and
            (newrow is None or newrow[0] is None)):
            lost_values[(station,var)]+=1
        events.append({'station':station,'date':day,'variable':var,'kind':kind,
                       'before':list(map(str,oldrow)) if oldrow else None,
                       'after':list(map(str,newrow)) if newrow else None})
    historical={station:sum(1 for x in events
                            if x['station']==station and x['date']<'2000-01-01'
                            and x['before'] is not None and x['before'][0]!='None'
                            and (x['after'] is None or x['after'][0]=='None'))
                for station,_ in lost_values}
    historical={k:v for k,v in sorted(historical.items()) if v}
    return {'schema':'dashi.bom.cdo.native_revision_result.v1',
            'before_receipts':old,'after_receipts':new,
            'before_rows':len(before),'after_rows':len(after),
            'counts':dict(sorted(counts.items())),
            'value_removals_by_station_product':{f'{s}:{v}':n for (s,v),n in sorted(removals.items())},
            'pre2000_observed_values_lost_by_station':historical,
            'values_lost_including_disappearing_calendar_rows':
                {f'{s}:{v}':n for (s,v),n in sorted(lost_values.items())},
            'author_reported_target_only':{'pre2000_total':571,'066062':515,
                                            '044022_or_044021':56},
            'pre2000_target_matched':sum(historical.values())==571
                                   and historical.get('066062')==515
                                   and sum(v for s,v in historical.items()
                                           if s in ('044022','044021'))==56,
            'source_identification':'BOM CDO-formatted rows with matching SHA256; publisher identity requires independent provenance',
            'original_paper_authenticated':False,
            'climate_impact_computed':False,'events':events}

def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--manifest',required=True,type=Path)
    p.add_argument('--output',type=Path)
    a=p.parse_args()
    manifest=json.loads(a.manifest.read_text(encoding='utf-8'))
    out=audit(manifest,a.manifest.parent)
    data=json.dumps(out,sort_keys=True,indent=2)+'\n'
    if a.output:a.output.write_text(data,encoding='utf-8')
    else:print(data,end='')
if __name__=='__main__':main()
