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

from inventory import digest, upstream_commit
from alignment import checked_alignment

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



def verify_source_receipts(recons_path: Path, images_path: Path, fmri_path: Path,
                           design_path: Path, subject: int, condition: str,
                           seed: int, branch: str, inference_receipt: Path | None,
                           inventory_receipt: Path | None) -> dict:
    """Require real inference output hashes AND upstream source/inventory identity.

    The Python evaluator's direct API may be used in toy tests without these
    receipts; those evaluations are visibly non-promotable. CLI requires both.
    """
    if inference_receipt is None and inventory_receipt is None:
        return {"admitted": False, "reason": "No source/inference receipts supplied"}
    if inference_receipt is None or inventory_receipt is None:
        raise ValueError("Both actual inference and source inventory receipts are required")
    run = json.loads(inference_receipt.read_text())
    inv = json.loads(inventory_receipt.read_text())
    if run.get("model_inference_executed") is not True or (
        run.get("upstream_inference_returned_successfully") is not True
    ):
        raise ValueError("No successful upstream inference receipt")
    if (run.get("condition"), run.get("seed"),
        run.get("subject_internal_zero_based")) != (condition, seed, subject - 1):
        raise ValueError("Input control condition/seed/subject receipt mismatch")
    if inv.get("status") != "artifact_inventory_complete_not_replayed":
        raise ValueError("Upstream artifacts are not fully identified")
    if subject not in inv.get("subjects_1_based", []):
        raise ValueError("Subject is outside frozen inventory")
    expected = (("fmri", fmri_path), ("ground_truth", images_path),
                ("nsd_design", design_path))
    for key, file in expected:
        if inv["artifacts"][key]["sha256"] != digest(file):
            raise ValueError(f"Source hash changed since inventory: {key}")
    for key in ("v2c_mapping",):
        recorded = inv["artifacts"][key]
        if recorded.get("status") != "present" or digest(
            Path(recorded["path"])
        ) != recorded["sha256"]:
            raise ValueError(f"Mapping changed since inventory: {key}")
    for checkpoint in inv["artifacts"]["checkpoints"]:
        if checkpoint.get("status") != "present" or digest(
            Path(checkpoint["path"])
        ) != checkpoint["sha256"]:
            raise ValueError("A frozen checkpoint changed since inventory")
    root = Path(inv["source"]["upstream_root"])
    revision, dirty = upstream_commit(root)
    if (revision, dirty) != (inv["source"]["actual_revision"], False):
        raise ValueError("Upstream source revision or working tree changed")
    if run.get("source_fmri_sha256") != digest(fmri_path):
        raise ValueError("Stage input is not a control of admitted source fMRI")
    stage_root = inference_receipt.parent.resolve()
    staged_input = stage_root / "data/nsd_data/fmri_v2.npz"
    if not staged_input.is_file() or digest(staged_input) != run.get(
        "controlled_fmri_sha256"
    ):
        raise ValueError("Actual controlled fMRI input has changed")
    actual_output = recons_path.resolve()
    eligible = [
        entry for entry in run.get("saved_arrays", [])
        if (stage_root / entry["path"]).resolve() == actual_output
        and entry["sha256"] == digest(actual_output)
        and Path(entry["path"]).name in (
            "enhanced_recons.npy", "semantic_recons.npy", "low_level_recons.npy")
    ]
    if not eligible or actual_output.name != f"{branch}_recons.npy":
        raise ValueError("Reconstruction array is not a checked upstream output")
    return {
        "admitted": True, "source_inventory_sha256": digest(inventory_receipt),
        "inference_receipt_sha256": digest(inference_receipt),
        "upstream_git_commit": inv["source"]["actual_revision"],
        "input_control": run["condition"],
    }

def evaluate(recons_path: Path, images_path: Path, fmri_path: Path,
             design_path: Path, subject: int, condition: str, seed: int,
             branch: str, gt_feat: Path | None = None,
             recon_feat: Path | None = None,
             feature_source: str | None = None,
             inference_receipt: Path | None = None,
             inventory_receipt: Path | None = None) -> dict:
    if not 1 <= subject <= 8:
        raise ValueError("subject is NSD 1-based (1..8)")
    proof = verify_source_receipts(
        recons_path, images_path, fmri_path, design_path,
        subject, condition, seed, branch, inference_receipt, inventory_receipt)
    recons = unit_images(np.load(recons_path, allow_pickle=False))
    originals = np.load(images_path, mmap_mode="r", allow_pickle=False)
    alignment = checked_alignment(fmri_path, design_path)
    ids = np.asarray(alignment["row_global_image_ids"])
    with np.load(fmri_path, allow_pickle=False) as ds:
        n_images = len(ds["type_sample"])
    if len(originals) != n_images or len(recons) > len(ids):
        raise ValueError("Cannot prove fMRI / image test-row correspondence")
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
                            "fmri": digest(fmri_path),
                            "nsd_design": digest(design_path)},
        "upstream_sorted_gt_order_matches_fmri":
            alignment["upstream_inference_gt_order_matches_fmri_rows"],
        "subject": subject, "condition": condition, "seed": seed,
        "branch": branch, "aggregate": aggregate,
        "feature_evaluation": feature_result, "rows": rows,
        "source_and_inference_receipts": proof,
        "benchmark_admissible": proof["admitted"],
        "replay_claim": ("Model output receipts checked; independent metric algorithm"
                         if proof["admitted"] else
                         "Not an independently verified upstream model replay"),
    }


def main(argv=None):
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--recons", type=Path, required=True)
    ap.add_argument("--images", type=Path, required=True)
    ap.add_argument("--fmri", type=Path, required=True)
    ap.add_argument("--design", type=Path, required=True,
                    help="Original NSD nsd_expdesign.mat to verify row identity")
    ap.add_argument("--subject", type=int, required=True, help="NSD number 1..8")
    ap.add_argument("--condition", choices=["paired", "deranged", "zero"], required=True)
    ap.add_argument("--seed", type=int, required=True)
    ap.add_argument("--branch", choices=["enhanced", "semantic", "low_level"], required=True)
    ap.add_argument("--feature-gt", type=Path)
    ap.add_argument("--feature-recons", type=Path)
    ap.add_argument("--feature-source", type=str)
    ap.add_argument("--inference-receipt", type=Path, required=True,
                    help="Generated by stage_conditions seeded wrapper after full run")
    ap.add_argument("--inventory", type=Path, required=True,
                    help="Complete source/inference checkpoint inventory")
    ap.add_argument("--out", type=Path, required=True)
    args = ap.parse_args(argv)
    report = evaluate(args.recons, args.images, args.fmri, args.design, args.subject,
                      args.condition, args.seed, args.branch,
                      args.feature_gt, args.feature_recons,
                      args.feature_source, args.inference_receipt, args.inventory)
    args.out.parent.mkdir(parents=True, exist_ok=True)
    args.out.write_text(json.dumps(report, indent=2, sort_keys=True) + "\n")
    print(json.dumps(report["aggregate"], indent=2))


if __name__ == "__main__":
    main()
