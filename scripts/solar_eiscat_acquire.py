#!/usr/bin/env python3
"""Catalogue acquisition and structural audit for the 18 Dec 2017 VHF event.
No conductance fit, physical flux admission, resampling or imputation.
Requires madrigalWeb for catalogue/download, h5py and numpy for audit.
"""
import argparse
import hashlib
import json
from datetime import datetime, timezone
from pathlib import Path

URL = 'https://madrigal.eiscat.se/madrigal/'
NAME = '2017-12-18_bella@vhf'
START = datetime(2017, 12, 18, 2, 30, tzinfo=timezone.utc).timestamp()
STOP = datetime(2017, 12, 18, 6, tzinfo=timezone.utc).timestamp()


def digest(path):
    h = hashlib.sha256()
    with path.open('rb') as f:
        for chunk in iter(lambda: f.read(1024 * 1024), b''):
            h.update(chunk)
    return h.hexdigest()


def audit(path):
    import h5py
    import numpy as np
    path = Path(path)
    with h5py.File(path, 'r') as f:
        table = f['Data/Table Layout']
        names = {k.lower(): k for k in table.dtype.names or ()}
        required = {'ut1_unix', 'ut2_unix', 'kinst', 'recno'}
        if not required <= names.keys():
            raise ValueError('Missing CEDAR prolog fields: ' + str(required - names.keys()))
        count = 0
        durations = set()
        instruments = set()
        first, last = float('inf'), -float('inf')
        stats = {}
        fields = [k for k in ('gdalt','range','azm','elm','gdlat','glon','ne','nel','dne','dnel','te','dte','ti','dti','vi','dvi','vo','dvo') if k in names]
        for key in fields:
            stats[key] = {'finite': 0, 'nonfinite': 0, 'negative': 0}
        for i in range(0, len(table), 100000):
            rows = table[i:i+100000]
            t0, t1 = rows[names['ut1_unix']], rows[names['ut2_unix']]
            if not np.all(np.isfinite(t0) & np.isfinite(t1) & (t1 >= t0)):
                raise ValueError('Invalid time interval')
            take = (t0 < STOP) & (t1 > START)
            if not np.any(take):
                continue
            t0, t1, rows = t0[take], t1[take], rows[take]
            count += len(rows)
            first, last = min(first, float(t0.min())), max(last, float(t1.max()))
            durations.update(map(float, np.unique(t1-t0)))
            instruments.update(map(int, np.unique(rows[names['kinst']])))
            for k in fields:
                v = rows[names[k]]
                finite = np.isfinite(v)
                stats[k]['finite'] += int(finite.sum())
                stats[k]['nonfinite'] += int((~finite).sum())
                stats[k]['negative'] += int((finite & (v < 0)).sum())
        if count == 0 or instruments != {74}:
            raise ValueError('No matching instrument-74 context rows')
        metadata = {}
        if 'Metadata/Data Parameters' in f:
            m = f['Metadata/Data Parameters']
            metadata = {'fields': list(m.dtype.names or ()), 'records': [str(x) for x in m[:]]}
        return {'status': 'STRUCTURAL_AUDIT_ONLY', 'sha256': digest(path), 'table_rows': len(table),
                'context_rows': count, 'first_start_utc': datetime.fromtimestamp(first, timezone.utc).isoformat(),
                'last_end_utc': datetime.fromtimestamp(last, timezone.utc).isoformat(),
                'record_interval_seconds': sorted(durations), 'instrument_codes': sorted(instruments),
                'raw_fields': sorted(names), 'raw_field_counts': stats, 'parameter_metadata': metadata,
                'physical_admission': False, 'conductance_replayed': False}


def catalogue():
    from madrigalWeb.madrigalWeb import MadrigalData
    client = MadrigalData(URL)
    exps = client.getExperiments(74, 2017, 12, 18, 0, 0, 0, 2017, 12, 19, 0, 0, 0)
    match = [e for e in exps if e.name.strip() == NAME and e.id > 0]
    if len(match) != 1:
        raise ValueError('Exact experiment not uniquely resolved: ' + str([(e.id,e.name) for e in exps]))
    files = client.getExperimentFiles(match[0].id)
    return client, match[0], files


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--audit', type=Path, help='Inspect an already downloaded original HDF5')
    p.add_argument('--file', help='Exact remote name from catalogue output; omit to list only')
    p.add_argument('--output', type=Path, default=Path('eiscat-20171218'))
    args = p.parse_args()
    if args.audit:
        print(json.dumps(audit(args.audit), indent=2)); return
    client, exp, files = catalogue()
    print(json.dumps({'experiment_id': exp.id, 'name': exp.name,
                      'files': [{'name': f.name, 'category': f.category, 'kindat': f.kindat,
                                 'description': str(f)} for f in files]}, indent=2))
    if args.file is None:
        return
    chosen = [f for f in files if f.name == args.file and f.category == 1]
    if len(chosen) != 1:
        raise ValueError('Select an exact default-category filename returned by the catalogue')
    args.output.mkdir(parents=True, exist_ok=True)
    dest = args.output / (Path(chosen[0].name).stem + '.hdf5')
    part = dest.with_suffix('.part.hdf5')
    if dest.exists() or part.exists():
        raise FileExistsError('Refusing to overwrite existing source or partial download')
    name, email, affiliation = (input(x + ': ').strip() for x in ('Name', 'Email', 'Affiliation'))
    if not all((name, email, affiliation)):
        raise ValueError('Madrigal requires actual user attribution details')
    client.downloadFile(chosen[0].name, str(part), name, email, affiliation, 'hdf5')
    result = audit(part)
    part.rename(dest)
    receipt = dict(result, experiment_id=exp.id, experiment_name=exp.name, remote_file=chosen[0].name,
                   catalogue_url=URL, local_file=str(dest))
    dest.with_suffix('.receipt.json').write_text(json.dumps(receipt, indent=2)+'\n')
    print(json.dumps(receipt, indent=2))


if __name__ == '__main__':
    main()
