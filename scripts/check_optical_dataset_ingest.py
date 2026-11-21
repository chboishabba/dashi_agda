"""Strict source-data CSV ingestion for the temporal-slit optical lane.

No published source data is bundled. Scientific claims require measured rows,
a source manifest, and separate complex-vs-intensity analysis.
"""
import argparse
import csv
import hashlib
import json
import math
from pathlib import Path
import tempfile

REQUIRED = ('frequency', 'intensity')

def ingest(csv_path, manifest_path, require_measured=True):
    raw=Path(csv_path).read_bytes()
    manifest=json.loads(Path(manifest_path).read_text(encoding='utf-8'))
    assert manifest.get('source_kind') in ('measured','synthetic'), 'declare source_kind'
    assert manifest.get('sha256')==hashlib.sha256(raw).hexdigest(), 'source hash mismatch'
    assert manifest.get('frequency_unit') and manifest.get('intensity_unit'), 'units required'
    assert manifest.get('source_reference'), 'source DOI/record required'
    if require_measured:
        assert manifest['source_kind']=='measured', 'synthetic fixture is not experimental replay'
    rows=list(csv.DictReader(raw.decode('utf-8-sig').splitlines()))
    assert rows, 'empty data'
    assert all(k in rows[0] for k in REQUIRED), 'frequency/intensity columns missing'
    spectrum=[]
    for row in rows:
        f=float(row['frequency']); intensity=float(row['intensity'])
        assert math.isfinite(f) and math.isfinite(intensity) and intensity>=0
        spectrum.append((f,intensity))
    assert all(spectrum[i][0]<spectrum[i+1][0] for i in range(len(spectrum)-1)), 'frequencies must be strictly increasing'
    return {'rows':len(spectrum),'frequency_min':spectrum[0][0], 'frequency_max':spectrum[-1][0], 'source_kind':manifest['source_kind'], 'sha256':manifest['sha256']}

def test():
    checks=0
    with tempfile.TemporaryDirectory() as td:
        path=Path(td)/'demo.csv';meta=Path(td)/'demo.manifest.json'
        path.write_text('frequency,intensity\n0,4\n1,2\n2,0\n',encoding='utf-8')
        manifest={'source_kind':'synthetic','sha256':hashlib.sha256(path.read_bytes()).hexdigest(), 'frequency_unit':'arbitrary', 'intensity_unit':'arbitrary', 'source_reference':'synthetic test fixture; NOT the 2023 optical data'}
        meta.write_text(json.dumps(manifest),encoding='utf-8')
        value=ingest(path,meta,require_measured=False)
        assert value['rows']==3;checks+=1
        try:ingest(path,meta,require_measured=True)
        except AssertionError:checks+=1
        else:raise AssertionError('synthetic accepted as measured')
        path.write_text('frequency,intensity\n0,4\n0,2\n',encoding='utf-8')
        manifest['sha256']=hashlib.sha256(path.read_bytes()).hexdigest();meta.write_text(json.dumps(manifest))
        try:ingest(path,meta,require_measured=False)
        except AssertionError:checks+=1
        else:raise AssertionError('duplicate frequency accepted')
        path.write_text('frequency,intensity\n0,4\n1,2\n',encoding='utf-8')
        try:ingest(path,meta,require_measured=False)
        except AssertionError:checks+=1
        else:raise AssertionError('tampered data accepted')
        manifest['sha256']=hashlib.sha256(path.read_bytes()).hexdigest();meta.write_text(json.dumps(manifest))
        assert ingest(path,meta,require_measured=False)['rows']==2;checks+=1
    print(f'{checks}/{checks} PASS synthetic CSV ingestion and fail-closed controls')

if __name__=='__main__':
    parser=argparse.ArgumentParser()
    parser.add_argument('csv',nargs='?');parser.add_argument('manifest',nargs='?')
    parser.add_argument('--test',action='store_true')
    args=parser.parse_args()
    if args.test:test()
    else:
        parser.error('pass both CSV and manifest or --test') if not args.csv or not args.manifest else print(json.dumps(ingest(args.csv,args.manifest),indent=2))
