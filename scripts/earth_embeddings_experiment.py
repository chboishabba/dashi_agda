#!/usr/bin/env python3
"""Leakage-controlled four-arm Earth embedding benchmark; no automatic downloads.

Input .npz arrays: alpha [N,64], tessera [N,128], baseline [N,B],
labels [N], cell [N], year [N], x [N], y [N], label_source [N].
External manifest.json must declare exact versions, spatial CRS, pixel scale,
observed target/unit, provenance, acquisition QA, and data license.
No results claimed for Woogaroo unless actual independent observations supplied.
"""
import argparse
import hashlib
import json
from pathlib import Path

import numpy as np
from sklearn.linear_model import Ridge
from sklearn.metrics import mean_absolute_error, mean_squared_error, r2_score
from sklearn.neighbors import NearestNeighbors

REQUIRED_META = ('alpha_source', 'alpha_version', 'tessera_source',
 'tessera_version', 'baseline_source', 'label_provenance', 'target',
 'target_unit', 'crs', 'pixel_size_metres', 'acquisition_qa',
 'data_license', 'observation_window')


def checked_array(a, name, shape_tail=None):
    if not np.issubdtype(a.dtype, np.number) and name not in ('cell', 'year', 'label_source'):
        raise ValueError(f'{name}: must be numeric')
    if shape_tail is not None and a.shape[1:] != shape_tail:
        raise ValueError(f'{name}: expected trailing shape {shape_tail}, got {a.shape}')
    if name not in ('cell', 'year', 'label_source') and not np.isfinite(a).all():
        raise ValueError(f'{name}: nonfinite values (do not silently impute)')


def load_inputs(npz_path, manifest_path):
    manifest = json.loads(Path(manifest_path).read_text(encoding='utf-8'))
    missing = [k for k in REQUIRED_META if not manifest.get(k)]
    if missing:
        raise ValueError(f'missing manifest fields: {missing}')
    with np.load(npz_path, allow_pickle=False) as data:
        required = {'alpha', 'tessera', 'baseline', 'labels', 'cell',
                    'year', 'x', 'y', 'label_source'}
        if required - set(data.files):
            raise ValueError(f'missing arrays: {sorted(required - set(data.files))}')
        arr = {name: data[name].copy() for name in required}
    n = len(arr['labels'])
    if n < 6 or any(a.shape[0] != n for a in arr.values()):
        raise ValueError('insufficient or misaligned rows')
    for name in ('alpha', 'tessera', 'baseline'):
        checked_array(arr[name], name, {'alpha': (64,), 'tessera': (128,)}.get(name))
    if arr['baseline'].ndim != 2 or arr['baseline'].shape[1] == 0:
        raise ValueError('baseline must be nonempty 2d numerical array')
    for name in ('labels', 'x', 'y'):
        checked_array(arr[name], name, ())
    for name in ('cell', 'year', 'label_source'):
        if arr[name].ndim != 1 or any(not str(s).strip() for s in arr[name]):
            raise ValueError(f'{name}: empty or non-1d')
    if len(set(zip(arr['cell'].tolist(), arr['year'].tolist()))) != n:
        raise ValueError('duplicate cell/year observations')
    return arr, manifest


def split_by_spatial_and_temporal_holdout(data, heldout_years, heldout_cells,
                                           buffer_distance=0.0):
    """Train excludes ALL test cells and test years. Test requires BOTH.

    Buffer is in supplied projected CRS units (expected metres). Intermediate
    rows are dropped; callers must not reinterpret them as test observations.
    """
    if buffer_distance < 0:
        raise ValueError('buffer must be nonnegative')
    year = np.asarray(data['year']).astype(str)
    cell = np.asarray(data['cell']).astype(str)
    test = np.isin(year, [str(y) for y in heldout_years]) & np.isin(cell, heldout_cells)
    train = ~np.isin(year, [str(y) for y in heldout_years]) & ~np.isin(cell, heldout_cells)
    if not train.any() or not test.any():
        raise ValueError('empty training or test fold')
    if buffer_distance:
        xy_train = np.column_stack((data['x'][train], data['y'][train]))
        xy_test = np.column_stack((data['x'][test], data['y'][test]))
        nearest = NearestNeighbors(n_neighbors=1).fit(xy_test)
        far = nearest.kneighbors(xy_train, return_distance=True)[0][:, 0] >= buffer_distance
        indices = np.flatnonzero(train)
        train[indices[~far]] = False
        if not train.any():
            raise ValueError('spatial buffer removes entire training fold')
    if set(cell[train]) & set(cell[test]):
        raise AssertionError('cell leakage')
    if set(year[train]) & set(year[test]):
        raise AssertionError('temporal leakage')
    if buffer_distance:
        from scipy.spatial.distance import cdist
        if np.min(cdist(np.column_stack((data['x'][train], data['y'][train])),
                        np.column_stack((data['x'][test], data['y'][test])))) < buffer_distance - 1e-8:
            raise AssertionError('buffer distance violation')
    return train, test


def participation_ratio(vectors):
    """Effective rank estimator trace(C)^2/trace(C^2), not manifold dimension."""
    x = np.asarray(vectors, dtype=float)
    if x.ndim != 2 or x.shape[0] < 2 or not np.isfinite(x).all():
        raise ValueError('need >=2 finite rows')
    singular = np.linalg.svd(x - x.mean(axis=0), compute_uv=False)
    eigenvalues = singular ** 2 / (len(x) - 1)
    denom = float(np.dot(eigenvalues, eigenvalues))
    return float(eigenvalues.sum() ** 2 / denom) if denom > 0 else 0.0


def local_pca_tangents(vectors, k=10, intrinsic=4):
    """Estimated local tangent *bases*, not proof of a differentiable manifold."""
    x = np.asarray(vectors, dtype=float)
    if x.ndim != 2 or len(x) <= k or not 0 < intrinsic <= min(k, x.shape[1]):
        raise ValueError('invalid local PCA neighbourhood')
    neighbours = NearestNeighbors(n_neighbors=k+1).fit(x)
    indices = neighbours.kneighbors(x, return_distance=False)[:, 1:]
    bases = []
    for ids in indices:
        patch = x[ids] - x[ids].mean(axis=0)
        _, _, vh = np.linalg.svd(patch, full_matrices=False)
        bases.append(vh[:intrinsic].T)
    return np.asarray(bases)


def tangent_rotation_angles(bases, reference=0):
    """Largest principal angle to reference subspace; degree output."""
    base = bases[reference]
    angles = []
    for other in bases:
        s = np.linalg.svd(base.T @ other, compute_uv=False)
        angles.append(float(np.degrees(np.arccos(np.clip(s.min(), -1, 1)))))
    return angles


def normalized_quantization_error(original, stored, per_coordinate_tolerance):
    if original.shape != stored.shape or per_coordinate_tolerance < 0:
        raise ValueError('shape mismatch or invalid tolerance')
    if not np.isfinite(original).all() or not np.isfinite(stored).all():
        raise ValueError('nonfinite quantisation inputs')
    err = np.abs(original - stored)
    max_error = float(err.max())
    if max_error > per_coordinate_tolerance + 1e-10:
        raise ValueError('quantisation certificate does not hold')
    return {'max_coordinate_error': max_error,
            'max_l2_error': float(np.linalg.norm(original-stored, axis=1).max()),
            'certified_l2_upper_bound': float(np.sqrt(original.shape[1]) * per_coordinate_tolerance)}


def evaluate(data, manifest, train, test, ridge_alpha=1.0):
    """All arms share the SAME folds and simple ridge head.

    Fitted scalers are computed only on training samples. Labels must be
    independently collected to warrant an environmental interpretation.
    """
    if ridge_alpha <= 0:
        raise ValueError('regularisation must be positive')
    y = data['labels'].astype(float)
    baseline = data['baseline'].astype(float)
    alpha = data['alpha'].astype(float)
    tessera = data['tessera'].astype(float)
    arms = {'M0_static': baseline,
            'MA_alpha': np.concatenate([baseline, alpha], axis=1),
            'MT_tessera': np.concatenate([baseline, tessera], axis=1),
            'MAT_fused': np.concatenate([baseline, alpha, tessera], axis=1)}
    metrics = {}
    for name, values in arms.items():
        means = values[train].mean(axis=0)
        scales = values[train].std(axis=0)
        scales[scales == 0] = 1
        reg = Ridge(alpha=ridge_alpha).fit((values[train]-means)/scales, y[train])
        predictions = reg.predict((values[test]-means)/scales)
        metrics[name] = {
            'MAE': float(mean_absolute_error(y[test], predictions)),
            'RMSE': float(np.sqrt(mean_squared_error(y[test], predictions))),
            'R2': float(r2_score(y[test], predictions)) if test.sum() > 1 else None,
            'prediction_count': int(test.sum()),
        }
    return {
      'method': 'identical Ridge(alpha) heads with train-fold-only standardisation',
      'status': 'empirical evaluation on user supplied arrays; not independently verified field truth',
      'manifest': manifest,
      'train_rows': int(train.sum()), 'test_rows': int(test.sum()),
      'unused_rows': int(len(y)-train.sum()-test.sum()),
      'train_years': sorted(set(np.asarray(data['year'])[train].astype(str))),
      'test_years': sorted(set(np.asarray(data['year'])[test].astype(str))),
      'alpha_participation_ratio_train': participation_ratio(alpha[train]),
      'tessera_participation_ratio_train': participation_ratio(tessera[train]),
      'metrics': metrics,
    }


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('npz'); p.add_argument('manifest'); p.add_argument('output')
    p.add_argument('--test-year', action='append', required=True)
    p.add_argument('--test-cell', action='append', required=True)
    p.add_argument('--buffer-metres', type=float, default=0)
    p.add_argument('--ridge-alpha', type=float, default=1)
    a = p.parse_args()
    data, manifest = load_inputs(a.npz, a.manifest)
    if not str(manifest['crs']).upper().startswith(('EPSG:28', 'EPSG:32')) and a.buffer_metres:
        raise ValueError('buffer requires explicitly projected metre CRS; inspect CRS units')
    train, test = split_by_spatial_and_temporal_holdout(data, a.test_year, a.test_cell, a.buffer_metres)
    receipt = evaluate(data, manifest, train, test, a.ridge_alpha)
    receipt['input_sha256'] = hashlib.sha256(Path(a.npz).read_bytes()).hexdigest()
    Path(a.output).write_text(json.dumps(receipt, indent=2, sort_keys=True)+'\n', encoding='utf-8')
    print(json.dumps(receipt['metrics'], indent=2))


if __name__ == '__main__':
    main()
