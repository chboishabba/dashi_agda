"""Independent, fail-closed Brain-IT input/checkpoint provenance inventory.

No data downloads or model executions. Record SHA-256 over the *actual* local
bytes, not placeholder digests or paper-reported results.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import subprocess
from pathlib import Path

import numpy as np

UPSTREAM_REPO = "https://github.com/WeizmannVision/brainit-fmri"
UPSTREAM_HEAD_INSPECTED = "a7663eb5002e9ea5f899815326ff52d45be9a2f3"
ARXIV = "2510.25976v2"


def digest(path: Path) -> str:
    h = hashlib.sha256()
    with path.open("rb") as f:
        for chunk in iter(lambda: f.read(4 * 1024 * 1024), b""):
            h.update(chunk)
    return h.hexdigest()


def file_record(path: Path | None) -> dict:
    if path is None:
        return {"status": "missing", "sha256": None}
    path = Path(path).expanduser().resolve()
    if not path.is_file():
        return {"status": "missing", "path": str(path), "sha256": None}
    return {"status": "present", "path": str(path), "bytes": path.stat().st_size,
            "sha256": digest(path)}


def upstream_commit(root: Path) -> tuple[str | None, bool | None]:
    if not (root / ".git").exists():
        return None, None
    try:
        sha = subprocess.check_output(
            ["git", "-C", str(root), "rev-parse", "HEAD"],
            text=True, stderr=subprocess.DEVNULL).strip()
        dirty = bool(subprocess.check_output(
            ["git", "-C", str(root), "status", "--porcelain"],
            text=True, stderr=subprocess.DEVNULL).strip())
        return sha, dirty
    except (OSError, subprocess.CalledProcessError):
        return None, None


def create_manifest(upstream: Path, fmri: Path, images: Path,
                    mapping: Path, checkpoints: list[Path],
                    subject_numbers: list[int], design: Path | None = None) -> dict:
    upstream = upstream.expanduser().resolve()
    sha, dirty = upstream_commit(upstream)
    artifacts = {
        "fmri": file_record(fmri), "ground_truth": file_record(images),
        "v2c_mapping": file_record(mapping), "nsd_design": file_record(design),
        "checkpoints": [file_record(p) for p in checkpoints],
    }
    status = "incomplete"
    shape = None
    alignment = None
    if artifacts["fmri"]["status"] == "present":
        with np.load(fmri, allow_pickle=False) as data:
            for key in ("multi_sub_fmri", "num_voxels_subjects", "type_sample"):
                if key not in data:
                    raise ValueError(f"Missing fMRI field {key}")
            n, total = data["multi_sub_fmri"].shape
            voxel_sizes = data["num_voxels_subjects"].astype(int).tolist()
            if total != sum(voxel_sizes):
                raise ValueError("fMRI voxel width differs from declared subject widths")
            n_test = int(np.count_nonzero(data["type_sample"] == 2))
            if n != n_test:
                raise ValueError("Cannot certify pairing: fMRI test rows != type_sample==2 count")
            shape = {"test_rows": int(n), "voxel_count": int(total),
                     "subject_voxel_counts": voxel_sizes,
                     "n_test_image_labels": n_test}
    base_present = all(artifacts[x]["status"] == "present"
                       for x in ("fmri", "ground_truth", "v2c_mapping"))
    required_checkpoints = {
        "combined_model.ckpt", "decoder_vgg_ext-1_batch64_save.pth",
        "decoder_clipg_ext-1_save.pth"}
    named_checkpoints = {Path(p).name for p in checkpoints}
    ckpt_present = required_checkpoints.issubset(named_checkpoints) and all(
        x["status"] == "present" for x in artifacts["checkpoints"])
    if artifacts["nsd_design"]["status"] == "present" and artifacts["fmri"]["status"] == "present":
        from alignment import checked_alignment
        a = checked_alignment(fmri, design)
        alignment = {
            "n_shared_samples": a["n_shared_samples"],
            "upstream_gt_order_matches_fmri_rows":
                a["upstream_inference_gt_order_matches_fmri_rows"],
            "requires_explicit_reordering":
                not a["upstream_inference_gt_order_matches_fmri_rows"],
        }
    if (base_present and ckpt_present and sha and dirty is False
            and shape is not None and alignment is not None):
        try:
            imgs = np.load(images, mmap_mode="r", allow_pickle=False)
            # This source file may contain all NSD stimuli, rather than only test stimuli.
            with np.load(fmri, allow_pickle=False) as d:
                source_image_count = len(d["type_sample"])
            if imgs.shape[0] != source_image_count:
                raise ValueError("Image count != total type_sample entries")
            status = "artifact_inventory_complete_not_replayed"
        except ValueError:
            raise
    return {
        "schema": "brainit-inventory-v1",
        "source": {"paper": ARXIV, "code_url": UPSTREAM_REPO,
                   "inspected_revision": UPSTREAM_HEAD_INSPECTED,
                   "actual_revision": sha, "git_dirty": dirty,
                   "upstream_root": str(upstream)},
        "subjects_1_based": subject_numbers,
        "minimum_required_checkpoint_names": sorted(required_checkpoints),
        "subjects_internal_zero_based": [n - 1 for n in subject_numbers],
        "artifacts": artifacts, "fmri_alignment": shape,
        "source_stimulus_alignment": alignment,
        "status": status,
        "independent_model_inference_performed": False,
        "paper_metric_reproduced": False,
        "warning": "An inventory is not a data licence, model replay, or benchmark receipt.",
    }


def main(argv=None):
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--upstream", type=Path, required=True)
    ap.add_argument("--fmri", type=Path, required=True)
    ap.add_argument("--images", type=Path, required=True)
    ap.add_argument("--mapping", type=Path, required=True)
    ap.add_argument("--design", type=Path,
                    help="NSD original experiment/nsd_expdesign.mat")
    ap.add_argument("--checkpoint", type=Path, action="append", default=[])
    ap.add_argument("--subjects", type=int, nargs="+", default=[1, 2, 5, 7])
    ap.add_argument("--out", type=Path, required=True)
    args = ap.parse_args(argv)
    if len(set(args.subjects)) != len(args.subjects) or any(
        s < 1 or s > 8 for s in args.subjects
    ):
        ap.error("subjects must be unique NSD 1-based IDs from 1 through 8")
    manifest = create_manifest(args.upstream, args.fmri, args.images,
                               args.mapping, args.checkpoint, args.subjects,
                               args.design)
    args.out.parent.mkdir(parents=True, exist_ok=True)
    args.out.write_text(json.dumps(manifest, indent=2, sort_keys=True) + "\n")
    print(manifest["status"])


if __name__ == "__main__":
    main()
