"""Verify NSD stimulus identity across independently ordered Brain-IT arrays.

Upstream prepare_fmri.py:
    mult_inds = subjectim[0][:1000] - 1
    multi_sub_fmri rows follow that mult_inds order.
Upstream full_inference.py:
    gt_imgs = nsd_images_224[type_sample == 2]
    selection follows sorted global image indices.
These orders might differ. Do not assume or silently re-pair them.
"""
from __future__ import annotations

import argparse
import json
from pathlib import Path

import numpy as np
from scipy.io import loadmat

from inventory import digest


def checked_alignment(fmri: Path, design: Path) -> dict:
    with np.load(fmri, allow_pickle=False) as ds:
        required = ("multi_sub_fmri", "type_sample")
        if any(k not in ds for k in required):
            raise ValueError("Missing fMRI test rows/type_sample")
        n = int(len(ds["multi_sub_fmri"]))
        mask = np.asarray(ds["type_sample"]) == 2
        globally_sorted_ids = np.flatnonzero(mask).astype(int)
    mat = loadmat(str(design))
    if "subjectim" not in mat:
        raise ValueError("Experiment design has no subjectim array")
    raw = np.asarray(mat["subjectim"])
    if raw.ndim != 2 or len(raw) < 1 or raw.shape[1] < n:
        raise ValueError("Malformed/short NSD subjectim")
    first_subject_ids = np.asarray(raw[0, :n], dtype=np.int64) - 1
    if np.any(first_subject_ids < 0):
        raise ValueError("Experiment design uses invalid 1-based image IDs")
    if n != len(globally_sorted_ids):
        raise ValueError("Shared test rows differ from type_sample==2 image count")
    if len(set(first_subject_ids.tolist())) != n:
        raise ValueError("Duplicate image identities in shared-stimulus sequence")
    if set(first_subject_ids.tolist()) != set(globally_sorted_ids.tolist()):
        raise ValueError("Shared fMRI/image identity sets do not agree")
    ordered = np.array_equal(first_subject_ids, globally_sorted_ids)
    sorted_pos = {int(x): i for i,x in enumerate(globally_sorted_ids)}
    return {
        "schema": "brainit-stimulus-alignment-v1",
        "source_fmri_sha256": digest(fmri),
        "nsd_experiment_design_sha256": digest(design),
        "n_shared_samples": n,
        "row_global_image_ids": first_subject_ids.tolist(),
        "globally_sorted_test_ids": globally_sorted_ids.tolist(),
        "row_to_sorted_test_position":
            [sorted_pos[int(x)] for x in first_subject_ids],
        "upstream_inference_gt_order_matches_fmri_rows": bool(ordered),
        "interpretation": "The independent evaluator uses row_global_image_ids."
                          " If false, upstream's unmodified inferred"
                          " ground-truth pairing requires explicit review.",
    }


def main(argv=None):
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--fmri", type=Path, required=True)
    ap.add_argument("--design", type=Path, required=True)
    ap.add_argument("--out", type=Path, required=True)
    args = ap.parse_args(argv)
    receipt = checked_alignment(args.fmri, args.design)
    args.out.parent.mkdir(parents=True, exist_ok=True)
    args.out.write_text(json.dumps(receipt, indent=2, sort_keys=True) + "\n")
    print(json.dumps({
        "n": receipt["n_shared_samples"],
        "upstream_pairing_order_matches":
            receipt["upstream_inference_gt_order_matches_fmri_rows"],
    }, indent=2))


if __name__ == "__main__":
    main()
