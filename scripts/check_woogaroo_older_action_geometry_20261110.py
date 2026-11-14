#!/usr/bin/env python3
"""EPBC 2019/8575 vs 2014/7306: provenance-bounded polygon overlap.

Original documents, CRS and legal effect require independent authentication.
Polygon inclusion does not establish legal exclusion or actual clearing.
"""
from __future__ import annotations
import argparse
import hashlib
import json
from pathlib import Path
from tempfile import TemporaryDirectory
from pyproj import CRS
from shapely.geometry import Polygon, MultiPolygon, mapping, shape
from shapely.ops import unary_union

CASE = 'EPBC 2019/8575'
ROLES = ('prior_approved_impact', 'prior_actual_clearing',
         'current_excluded_habitat', 'current_final_impact')
MAX_BYTES = 40 * 1024 * 1024
# Local metric grids used by the original 2014/7306 map and potential
# GDA2020 successor. Never infer that *any* metre CRS is area-safe.
ALLOWED_LOCAL_CRS = ('EPSG:28356', 'EPSG:7856')


def load_geom(root, record, role):
    if not isinstance(record, dict):
        raise ValueError(f'{role}: source record missing')
    rel, digest = record.get('file'), record.get('sha256')
    if (not isinstance(rel, str) or not rel or not isinstance(digest, str)
            or len(digest) != 64 or any(c not in '0123456789abcdef' for c in digest)):
        raise ValueError(f'{role}: source file and lowercase SHA-256 required')
    file = (root / rel).resolve()
    if not file.is_relative_to(root.resolve()) or not file.is_file():
        raise ValueError(f'{role}: missing file or path outside manifest directory')
    if not 0 < file.stat().st_size <= MAX_BYTES:
        raise ValueError(f'{role}: empty or oversized GeoJSON')
    raw = file.read_bytes()
    if hashlib.sha256(raw).hexdigest() != digest:
        raise ValueError(f'{role}: digest mismatch')
    data = json.loads(raw)
    if not isinstance(data, dict) or data.get('type') != 'FeatureCollection':
        raise ValueError(f'{role}: FeatureCollection required')
    features = data.get('features')
    if not isinstance(features, list) or not features:
        raise ValueError(f'{role}: nonempty polygons required')
    geometries = []
    for feature in features:
        if not isinstance(feature, dict) or feature.get('type') != 'Feature' or not feature.get('geometry'):
            raise ValueError(f'{role}: invalid feature')
        geom = shape(feature['geometry'])
        if not isinstance(geom, (Polygon, MultiPolygon)) or not geom.is_valid or geom.is_empty:
            raise ValueError(f'{role}: invalid/nonpolygon geometry')
        geometries.append(geom)
    combined = unary_union(geometries)
    if not combined.is_valid or combined.is_empty:
        raise ValueError(f'{role}: invalid union')
    return combined, digest


def audit(manifest, root):
    if not isinstance(manifest, dict) or manifest.get('case') != CASE:
        raise ValueError('Wrong case')
    epsg = manifest.get('projected_crs')
    if not isinstance(epsg, str) or not epsg.startswith('EPSG:'):
        raise ValueError('Explicit projected CRS required')
    crs = CRS.from_user_input(epsg)
    if not crs.is_projected or not all(x.unit_name.lower() in ('metre', 'meter') for x in crs.axis_info[:2]):
        raise ValueError('Projected metre CRS required, not latitude/longitude')
    if epsg not in ALLOWED_LOCAL_CRS:
        raise ValueError('Unsupported area-distorting or non-local CRS: no automatic reprojection')
    records = manifest.get('layers')
    if not isinstance(records, dict) or set(records) != set(ROLES):
        raise ValueError('Exactly four layer roles required')
    geoms, hashes = {}, {}
    for role in ROLES:
        record = records[role]
        if not isinstance(record, dict) or record.get('projected_crs') != epsg:
            raise ValueError(f'{role}: CRS mismatch')
        geoms[role], hashes[role] = load_geom(Path(root), record, role)
    prior = geoms['prior_approved_impact']
    cleared = geoms['prior_actual_clearing']
    excluded = geoms['current_excluded_habitat']
    current = geoms['current_final_impact']
    ha = lambda g: round(g.area / 10000, 8)
    not_prior = excluded.difference(prior)
    not_cleared = excluded.difference(cleared)
    not_current = excluded.difference(current)
    areas = {
        'prior_approved_impact': ha(prior),
        'prior_actual_clearing': ha(cleared),
        'current_excluded_habitat': ha(excluded),
        'current_final_impact': ha(current),
        'excluded_within_prior_approved': ha(excluded.intersection(prior)),
        'excluded_within_prior_actual_clearing': ha(excluded.intersection(cleared)),
        'excluded_within_current_impact': ha(excluded.intersection(current)),
        'excluded_outside_prior_approved': ha(not_prior),
        'excluded_outside_prior_actual_clearing': ha(not_cleared),
        'excluded_outside_current_impact': ha(not_current),
        'current_impact_overlap_prior_approved': ha(current.intersection(prior)),
        'prior_clearing_outside_prior_approval': ha(cleared.difference(prior))
    }
    return {
        'case': CASE, 'status': 'UNAUTHENTICATED_GEOMETRIC_CANDIDATE_COMPARISON',
        'projected_crs': epsg, 'original_layer_sha256': hashes,
        'local_mga_grid_areas_not_geodesic': True,
        'cross_datum_reprojection_performed': False,
        'area_hectares': areas,
        'excluded_inside_prior_approval': not_prior.is_empty,
        'excluded_inside_prior_actual_clearing': not_cleared.is_empty,
        'excluded_inside_current_impact': not_current.is_empty,
        'historical_reported_exclusion_ha': 7.6,
        'historical_7_6ha_matches_geometric_area_within_0_01ha':
            abs(ha(excluded)-7.6) <= 0.01,
        'source_authority_verified': False,
        'source_crs_independently_verified': False,
        'same_habitat_class_confirmed': False,
        'actual_clearing_independently_confirmed': False,
        'lawful_exclusion_established': False,
        'approval_breach_determined': False
    }


def selftest():
    import copy
    with TemporaryDirectory() as directory:
        root = Path(directory)
        epsg = 'EPSG:7856'  # Synthetic projected metric coordinates
        def source(role, vertices, crs=epsg):
            content = json.dumps({'type': 'FeatureCollection', 'features': [
                {'type': 'Feature', 'properties': {}, 'geometry': mapping(Polygon(vertices))}
            ]}, sort_keys=True).encode('utf-8')
            file = root / f'{role}-{len(list(root.iterdir()))}.geojson'
            file.write_bytes(content)
            return {'file': file.name, 'sha256': hashlib.sha256(content).hexdigest(),
                    'projected_crs': crs}
        square = [(500000,7000000),(500380,7000000),(500380,7000200),(500000,7000200)]
        manifest = {'case':CASE, 'projected_crs':epsg,
                    'layers':{role:source(role,square) for role in ROLES}}
        tests = 0
        good = audit(manifest, root)
        assert good['area_hectares']['current_excluded_habitat'] == 7.6
        assert good['excluded_inside_prior_approval'] and good['excluded_inside_prior_actual_clearing']
        tests += 1
        assert good['lawful_exclusion_established'] is False
        tests += 1
        moved = copy.deepcopy(manifest)
        shifted = [(501000,7000000),(501380,7000000),(501380,7000200),(501000,7000200)]
        moved['layers']['prior_actual_clearing'] = source('shifted',shifted)
        result = audit(moved, root)
        assert result['excluded_inside_prior_approval']
        assert result['area_hectares']['excluded_within_prior_actual_clearing'] == 0
        tests += 1
        tampered = copy.deepcopy(manifest)
        tampered['layers']['prior_approved_impact']['sha256'] = '0'*64
        try: audit(tampered,root); raise AssertionError('digest accepted')
        except ValueError as exc: assert 'digest mismatch' in str(exc)
        tests += 1
        geographic = copy.deepcopy(manifest)
        geographic['projected_crs'] = 'EPSG:4326'
        try: audit(geographic,root); raise AssertionError('degrees accepted')
        except ValueError as exc: assert 'Projected metre' in str(exc)
        tests += 1
        mercator = copy.deepcopy(manifest)
        mercator['projected_crs'] = 'EPSG:3857'
        for record in mercator['layers'].values():
            record['projected_crs'] = 'EPSG:3857'
        try: audit(mercator,root); raise AssertionError('Web Mercator area accepted')
        except ValueError as exc: assert 'Unsupported area-distorting' in str(exc)
        tests += 1
        mixed = copy.deepcopy(manifest)
        mixed['layers']['current_final_impact']['projected_crs'] = 'EPSG:4326'
        try: audit(mixed,root); raise AssertionError('mixed CRS accepted')
        except ValueError as exc: assert 'CRS mismatch' in str(exc)
        tests += 1
        absent = copy.deepcopy(manifest)
        del absent['layers']['prior_actual_clearing']
        try: audit(absent,root); raise AssertionError('missing layer accepted')
        except ValueError as exc: assert 'four layer' in str(exc)
        tests += 1
        escaped = copy.deepcopy(manifest)
        escaped['layers']['prior_actual_clearing']['file'] = '../outside.geojson'
        try: audit(escaped,root); raise AssertionError('path escape accepted')
        except ValueError as exc: assert 'outside' in str(exc)
        tests += 1
        wrong = copy.deepcopy(manifest)
        wrong['case'] = 'EPBC 2014/7306'
        try: audit(wrong,root); raise AssertionError('wrong case accepted')
        except ValueError as exc: assert 'Wrong case' in str(exc)
        tests += 1
        assert tests == 10
        return {'tests':tests, 'passed':tests, 'synthetic_only':True,
                'original_approval_or_clearing_polygons_acquired':False}


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--manifest',type=Path)
    ap.add_argument('--out',type=Path)
    ap.add_argument('--self-test',action='store_true')
    args = ap.parse_args()
    result = selftest() if args.self_test else (
        audit(json.loads(args.manifest.read_text()), args.manifest.resolve().parent)
        if args.manifest else ap.error('Need --self-test or --manifest'))
    output = json.dumps(result,sort_keys=True,indent=2) + '\n'
    if args.out: args.out.write_text(output,encoding='utf-8')
    print(output,end='')


if __name__ == '__main__':
    main()
