#!/usr/bin/env python3
"""Optional live Earth Engine + GeoTessera co-located sample extractor.

Requires network, earthengine-api authenticated project, and geotessera data
coverage. Inputs are independently labelled field sampling locations; a user
must supply the real Woogaroo study polygon and labels separately. This script
never invents missing cells, labels, imagery, or model versions.

Public references:
https://developers.google.com/earth-engine/datasets/catalog/GOOGLE_SATELLITE_EMBEDDING_V1_ANNUAL
https://github.com/ucam-eo/geotessera
"""
import argparse
import csv
import json
from pathlib import Path

import numpy as np
from pyproj import Transformer

ALPHA_BANDS = tuple(f'A{i:02d}' for i in range(64))


def read_sampling_locations(path, crs='EPSG:32756'):
    with Path(path).open(newline='', encoding='utf-8') as handle:
        records = list(csv.DictReader(handle))
    if not records:
        raise ValueError('no independent sampling observations')
    baseline_names = sorted(k for k in records[0] if k.startswith('baseline_'))
    if not baseline_names:
        raise ValueError('require at least one non-embedding baseline feature')
    to_metre = Transformer.from_crs('EPSG:4326', crs, always_xy=True)
    results = []
    for i, row in enumerate(records):
        try:
            lon, lat, year = float(row['lon']), float(row['lat']), int(row['year'])
            label = float(row['label'])
            x, y = to_metre.transform(lon, lat)
            baseline = [float(row[k]) for k in baseline_names]
        except (ValueError, KeyError) as error:
            raise ValueError(f'row {i}: incomplete coordinates/year/target/features') from error
        if not (-180 <= lon <= 180 and -90 <= lat <= 90 and 2017 <= year <= 2025):
            raise ValueError(f'row {i}: invalid observation coordinates or annual window')
        if not all(np.isfinite(v) for v in [x,y,label,*baseline]):
            raise ValueError(f'row {i}: nonfinite numeric values')
        if not row.get('label_source', '').strip():
            raise ValueError(f'row {i}: independent label source required')
        cell = f'{int(np.floor(x/10))}:{int(np.floor(y/10))}'
        results.append(dict(lon=lon,lat=lat,year=year,x=x,y=y,cell=cell,
            label=label,baseline=baseline,label_source=row['label_source']))
    pairs = [(r['cell'],r['year']) for r in results]
    if len(set(pairs)) != len(pairs):
        raise ValueError('duplicate 10m cell/year in independently labelled input')
    return results, baseline_names


def sample_alphaearth(records, project, chunk=30):
    import ee  # Optional external API, requires credentials.
    ee.Initialize(project=project)
    output = np.full((len(records), 64), np.nan)
    years = sorted(set(r['year'] for r in records))
    for year in years:
        ids = [i for i, r in enumerate(records) if r['year'] == year]
        image = (ee.ImageCollection('GOOGLE/SATELLITE_EMBEDDING/V1/ANNUAL')
            .filterDate(f'{year}-01-01', f'{year+1}-01-01')
            .select(list(ALPHA_BANDS)).mosaic())
        for start in range(0, len(ids), chunk):
            batch = ids[start:start+chunk]
            points = ee.FeatureCollection([
                ee.Feature(ee.Geometry.Point([records[i]['lon'], records[i]['lat']]),
                           {'source_row': i}) for i in batch])
            found = image.sampleRegions(collection=points,
                properties=['source_row'], scale=10, geometries=False).getInfo()['features']
            for feature in found:
                props = feature['properties']
                idx = int(props['source_row'])
                output[idx] = [props.get(k, np.nan) for k in ALPHA_BANDS]
    if not np.isfinite(output).all():
        missing = np.flatnonzero(~np.isfinite(output).all(axis=1))
        raise ValueError(f'AlphaEarth missing/no-data samples at rows {missing[:20].tolist()}')
    return output


def sample_tessera(records):
    from geotessera import GeoTesseraZarr  # Optional; public v1.1 may be used.
    gt = GeoTesseraZarr()
    output = np.full((len(records), 128), np.nan)
    for year in sorted(set(r['year'] for r in records)):
        indices = [i for i, r in enumerate(records) if r['year'] == year]
        values = gt.sample_points([(records[i]['lon'], records[i]['lat']) for i in indices],
                                  year=year)
        if values.shape != (len(indices),128):
            raise ValueError(f'TESSERA missing/wrong dimensionality in {year}: {values.shape}')
        output[indices] = values
    if not np.isfinite(output).all():
        missing = np.flatnonzero(~np.isfinite(output).all(axis=1))
        raise ValueError(f'TESSERA coverage/no-data issue at rows {missing[:20].tolist()}')
    return output


def assemble(records, alpha, tessera):
    if alpha.shape != (len(records),64) or tessera.shape != (len(records),128):
        raise ValueError('extracted vectors must match input rows exactly')
    return dict(alpha=alpha, tessera=tessera,
        baseline=np.array([r['baseline'] for r in records], dtype=float),
        labels=np.array([r['label'] for r in records], dtype=float),
        cell=np.array([r['cell'] for r in records]),
        year=np.array([r['year'] for r in records]),
        x=np.array([r['x'] for r in records]),
        y=np.array([r['y'] for r in records]),
        label_source=np.array([r['label_source'] for r in records]))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('locations_csv'); parser.add_argument('output_npz')
    parser.add_argument('--ee-project', required=True)
    parser.add_argument('--crs', default='EPSG:32756')
    parser.add_argument('--tessera-version', required=True,
        help='User-verified GeoTessera dataset/release identifier; do not assume v2')
    a=parser.parse_args()
    points, features=read_sampling_locations(a.locations_csv, a.crs)
    result=assemble(points, sample_alphaearth(points,a.ee_project), sample_tessera(points))
    np.savez_compressed(a.output_npz, **result)
    metadata={'crs':a.crs,'features':features,'rows':len(points),
              'source_alpha':'Google Satellite Embedding V1',
              'source_tessera_declared':a.tessera_version,
              'warning':'Version supplied by caller; independently verify configured GeoTessera store.',
              'status':'co-located sampled points only; no ecological validation'}
    Path(str(a.output_npz)+'.extraction.json').write_text(json.dumps(metadata,indent=2))


if __name__=='__main__':
    main()
