"""Google AlphaEarth V1 COG dequantisation and proper coarse aggregation.

Google docs: https://developers.google.com/earth-engine/guides/aef_on_gcs_readme
Signed-int8 raw values are not linearly encoded embeddings. Avoid plain
rasterio.average on raw channels. Handle zero-vector pooling explicitly.
"""
import numpy as np


def decode_signed_int8(raw):
    raw = np.asarray(raw)
    if raw.dtype != np.int8 or raw.shape[-1] != 64:
        raise ValueError('expected signed int8 with last dimension 64')
    scaled = raw.astype(np.float64) / 127.5
    return np.sign(scaled) * scaled ** 2


def normalized_aggregate(vectors, weights=None):
    x = np.asarray(vectors, dtype=float)
    if x.ndim != 2 or x.shape[1] != 64 or not len(x):
        raise ValueError('expected nonempty N x 64 vectors')
    if not np.isfinite(x).all():
        raise ValueError('missing or nonfinite vectors')
    w = np.ones(len(x)) if weights is None else np.asarray(weights, dtype=float)
    if w.shape != (len(x),) or not np.isfinite(w).all() or np.any(w < 0) or w.sum() == 0:
        raise ValueError('invalid aggregation weights')
    summed = np.einsum('ij,i->j', x, w)
    mag = np.linalg.norm(summed)
    if mag <= 1e-12:
        raise ValueError('aggregation cancels to a zero vector; direction undefined')
    return summed / mag


def aggregation_stability_bound(reference_sum_norm, weighted_sum_errors):
    """If ||S||>e, then ||S/||S||-(S+D)/||S+D|||| <=2e/(||S||-e).

    Caller supplies CERTIFIED norm bound e >= ||D||. This is a weak
    but useful analytic bound, not an error estimate inferred from a dtype.
    """
    q, e = float(reference_sum_norm), float(weighted_sum_errors)
    if not np.isfinite([q,e]).all() or q <= e or e < 0:
        raise ValueError('normalisation not stable under declared error bound')
    return 2 * e / (q - e)
