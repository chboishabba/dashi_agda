"""Evaluate independent Brain-IT reconstruction arrays against source-aligned NSD images.

Our PixCorr/SSIM are transparent numerical *proxies* for the paper's metrics,
not bitwise replays of the full authors' evaluator (which uses torchvision
resizing and separate learned feature networks). Never label the optional
2-way feature score '1000-way CLIP'. No imaginary benchmark scores.
"""
from __future__ import annotations

import argparse
import json
import csv
from pathlib import Path
from typing import Any

import numpy as np
from skimage.color import rgb2gray
from skimage.metrics import structural_similarity
from skimage.transform import resize

from inventory import digest

METRIC_VERSION = "brainit-independent-pixcorr-ssim425-v1"


def unit_images(x: np.ndarray) -> np.ndarray:
    """Reject silently clipping or normalising unknown image scales."""
    if x.ndim != 4 or x.shape[-1] != 3 or x.shape[1] != x.shape[2]:
        raise ValueError("Expected square N,H,W,3 colour images")
    if not np.isfinite(x).all():
        raise ValueError("NaN/Inf image values cannot be evaluated")
    if x.dtype == np.uint8:
        return x.astype(np.float32) / 255
    if np.issubdtype(x.dtype, np.floating):
        if float(x.min()) < 0 or float(x.max()) > 1:
            raise ValueError("Float images must be in [0,1], never auto-rescale")
        return x.astype(np.float32)
    raise ValueError("Expected uint8 [0,255] or float images [0,1]")


def pixel_corr(a: np.ndarray, b: np.ndarray) -> float | None:
    x = a.ravel().astype(np.float64)
    y = b.ravel().astype(np.float64)
    x -= x.mean()
    y -= y.mean()
    den = np.linalg.norm(x) * np.linalg.norm(y)
    return float(np.dot(x, y) / den) if den > 0 else None


def scores_one(reconstructed: np.ndarray, original: np.ndarray) -> dict[str, Any]:
    if reconstructed.shape != original.shape:
        raise ValueError("Image shapes must agree")
    r = resize(reconstructed, (425, 425, 3), order=1,
               anti_aliasing=True, preserve_range=True)
    g = resize(original, (425, 425, 3), order=1,
               anti_aliasing=True, preserve_range=True)
    ss = structural_similarity(
        rgb2gray(r), rgb2gray(g),
        gaussian_weights=True, sigma=1.5,
        use_sample_covariance=False, data_range=1.0)
    return {"pixcorr": pixel_corr(r, g), "ssim": float(ss)}


def two_way_feature_identification(recon_feat: np.ndarray,
                                   gt_feat: np.ndarray) -> float:
    """Fraction of *other* test candidates beaten by the true test target.

    This tests exactly the declared feature model and candidate pool, not
    a fixed 1000-way evaluation; ties count as failure, like upstream's
    strict correlation comparison.
    """
    r = np.asarray(recon_feat, dtype=float)
    g = np.asarray(gt_feat, dtype=float)
    if r.shape != g.shape or r.ndim != 2 or len(r) < 2:
        raise ValueError("Feature inputs require matching N,D (N>=2)")
    if not np.isfinite(r).all() or not np.isfinite(g).all():
        raise ValueError("Nonfinite feature vectors")
    r = r - r.mean(axis=1, keepdims=True)
    g = g - g.mean(axis=1, keepdims=True)
    rd = np.linalg.norm(r, axis=1, keepdims=True)
    gd = np.linalg.norm(g, axis=1, keepdims=True)
    if np.any(rd == 0) or np.any(gd == 0):
        raise ValueError("Constant features make correlation undefined")
    scores = (r / rd) @ (g / gd).T
    gt_scores = scores.diagonal()[:, None]
    better_than_distractor = scores < gt_scores
    np.fill_diagonal(better_than_distractor, False)
    return float(better_than_distractor.sum() / (len(r) * (len(r) - 1)))


def evaluate(recons_path: Path, images_path: Path, fmri_path: Path,
             subject: int, condition: str, seed: int,
             branch: str, gt_feat: Path | None = None,
             recon_feat: Path | None = None,
             feature_source: str | None = None) -> dict:
    if not 1 <= subject <= 8:
        raise ValueError("subject is NSD 1-based (1..8)")
    recons = unit_images(np.load(recons_path, allow_pickle=False))
    originals = np.load(images_path, mmap_mode="r", allow_pickle=False)
    with np.load(fmri_path, allow_pickle=False) as ds:
        source_mask = ds["type_sample"] == 2
        ids = np.flatnonzero(source_mask)
        n_fmri = len(ds["multi_sub_fmri"])
    if len(ids) != n_fmri or len(originals) != len(source_mask):
        raise ValueError("Cannot prove fMRI / image test-row correspondence")
    if len(recons) > len(ids):
        raise ValueError("More reconstructions than labelled test samples")
    truth = unit_images(np.asarray(originals[ids[:len(recons)]]))
    if truth.shape != recons.shape:
        raise ValueError("Ground truth / reconstruction dimensions differ")
    rows = []
    for i, (recon, gt) in enumerate(zip(recons, truth)):
        row = {"subject": subject, "condition": condition, "seed": seed,
               "branch": branch, "stimulus_id": int(ids[i]),
               "test_row": i, **scores_one(recon, gt)}
        rows.append(row)
    aggregate = {}
    for metric in ("pixcorr", "ssim"):
        valid = [r[metric] for r in rows if r[metric] is not None]
        aggregate[metric] = {"mean": float(np.mean(valid)) if valid else None,
                             "valid": len(valid), "total": len(rows)}
    feature_result = None
    if (gt_feat is None) != (recon_feat is None):
        raise ValueError("Both feature arrays must be supplied")
    if gt_feat is not None:
        if not feature_source:
            raise ValueError("Feature arrays require a named encoder source")
        gt = np.load(gt_feat, allow_pickle=False)
        rec = np.load(recon_feat, allow_pickle=False)
        if len(gt) != len(recons) or len(rec) != len(recons):
            raise ValueError("Feature row alignment mismatch")
        feature_result = {
            "source": feature_source, "two_way_identification": 
                two_way_feature_identification(rec, gt),
            "candidate_count": len(gt), "not_1000_way_clip": True,
            "gt_sha256": digest(gt_feat), "recon_sha256": digest(recon_feat)}
    return {
        "schema": "brainit-reconstruction-evaluation-v1",
        "metric_version": METRIC_VERSION,
        "scope": "independent image-metric evaluation, not the published evaluator",
        "source_paper": "Beliy et al., arXiv:2510.25976v2",
        "upstream_image_preprocess": "skimage resize 425x425 bilinear anti_alias, grayscale SSIM",
        "subjects_are_nsd_one_based": True,
        "artifact_hashes": {"recon": digest(recons_path),
                            "images": digest(images_path),
                            "fmri": digest(fmri_path)},
        "subject": subject, "condition": condition, "seed": seed,
        "branch": branch, "aggregate": aggregate,
        "feature_evaluation": feature_result, "rows": rows,
        "replay_claim": "not independently re-run model here",
    }


def main(argv=None):
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--recons", type=Path, required=True)
    ap.add_argument("--images", type=Path, required=True)
    ap.add_argument("--fmri", type=Path, required=True)
    ap.add_argument("--subject", type=int, required=True, help="NSD number 1..8")
    ap.add_argument("--condition", choices=["paired", "deranged", "zero"], required=True)
    ap.add_argument("--seed", type=int, required=True)
    ap.add_argument("--branch", choices=["enhanced", "semantic", "low_level"], required=True)
    ap.add_argument("--feature-gt", type=Path)
    ap.add_argument("--feature-recons", type=Path)
    ap.add_argument("--feature-source", type=str)
    ap.add_argument("--out", type=Path, required=True)
    args = ap.parse_args(argv)
    report = evaluate(args.recons, args.images, args.fmri, args.subject,
                      args.condition, args.seed, args.branch,
                      args.feature_gt, args.feature_recons,
                      args.feature_source)
    args.out.parent.mkdir(parents=True, exist_ok=True)
    args.out.write_text(json.dumps(report, indent=2, sort_keys=True) + "\n")
    print(json.dumps(report["aggregate"], indent=2))


if __name__ == "__main__":
    main()
