"""Stage *real input-fMRI* control experiments without modifying upstream data.

Not an inference result. Runs require the authors' downloaded artifacts and GPU.
We isolate the authors' code, models and data read-only via symlinks; results
are written to a new staging directory. Do not infer causality from zero-input
OOD controls or mismatched samples without paired metrics and uncertainty.
"""
from __future__ import annotations

import argparse
import json
import os
from pathlib import Path

import numpy as np

from inventory import digest

CONDITIONS = ("paired", "deranged", "zero")
REQUIRED = ("multi_sub_fmri", "num_voxels_subjects", "type_sample")
SEED_WRAPPER = '''"""Deterministically seed the unmodified upstream CLI (best effort)."""
import runpy
import sys
import random
import numpy as np
import torch
seed = int(sys.argv[1])
sys.argv = ["inference/full_inference.py"] + sys.argv[2:]
random.seed(seed)
np.random.seed(seed)
torch.manual_seed(seed)
if torch.cuda.is_available():
    torch.cuda.manual_seed_all(seed)
runpy.run_path("inference/full_inference.py", run_name="__main__")
'''


def derangement(n: int, seed: int) -> np.ndarray:
    """Uniform random cyclic assignment (not a uniform random derangement)."""
    if n < 2:
        raise ValueError("Derangement requires >=2 held-out test examples")
    rng = np.random.default_rng(seed)
    order = rng.permutation(n)
    perm = np.empty(n, dtype=np.int64)
    perm[order] = np.roll(order, 1)
    assert np.all(perm != np.arange(n))
    return perm


def controlled_fmri(path: Path, condition: str, subject_index: int,
                    seed: int) -> tuple[dict[str, np.ndarray], list[int]]:
    if condition not in CONDITIONS:
        raise ValueError("unknown condition")
    with np.load(path, allow_pickle=False) as ds:
        if not all(k in ds.files for k in REQUIRED):
            raise ValueError("Source NPZ missing required fields")
        # The official prepare_fmri.py emits a large single-subject array and
        # a pickled object 'type_desc'. Inference reads ONLY these three
        # numeric keys. Repacking all keys is unsafe/needlessly memory-heavy.
        arrays = {key: np.array(ds[key], copy=True) for key in REQUIRED}
    x = arrays["multi_sub_fmri"]
    sizes = arrays["num_voxels_subjects"].astype(int)
    if x.ndim != 2 or len(sizes) == 0 or any(sizes <= 0):
        raise ValueError("Invalid source subject/voxel geometry")
    if subject_index < 0 or subject_index >= len(sizes):
        raise ValueError("Subject index out of source range (0-based)")
    if x.shape[1] != int(sizes.sum()):
        raise ValueError("Subject voxel widths do not cover fMRI matrix")
    if int(np.count_nonzero(arrays["type_sample"] == 2)) != x.shape[0]:
        raise ValueError("Cannot establish NSD test-row alignment")
    start, end = int(sizes[:subject_index].sum()), int(sizes[:subject_index+1].sum())
    permutation = list(range(len(x)))
    if condition == "deranged":
        permutation = derangement(len(x), seed).tolist()
        x[:, start:end] = x[np.array(permutation), start:end]
    elif condition == "zero":
        x[:, start:end] = 0
    arrays["multi_sub_fmri"] = x
    return arrays, permutation


def _link(source: Path, dest: Path):
    if not source.exists():
        raise FileNotFoundError(f"Missing upstream resource: {source}")
    dest.parent.mkdir(parents=True, exist_ok=True)
    dest.symlink_to(source.resolve(), target_is_directory=source.is_dir())


def stage(upstream: Path, out: Path, condition: str,
          subject_index: int, seed: int, test: bool = True) -> dict:
    upstream = upstream.expanduser().resolve()
    out = out.expanduser().resolve()
    if out.exists():
        raise FileExistsError(f"Fail closed: refusing to overwrite staged run {out}")
    if not (upstream / "inference/full_inference.py").is_file():
        raise FileNotFoundError("Expected original Brain-IT inference script")
    if test and subject_index != 0:
        raise ValueError("Upstream --test hardcodes subject index 0; use full mode")
    source = upstream / "data/nsd_data/fmri_v2.npz"
    if not source.is_file():
        raise FileNotFoundError("Missing preprocessed human NSD fMRI")
    arrays, permutation = controlled_fmri(source, condition, subject_index, seed)
    out.mkdir(parents=True)
    for directory in ("models", "src", "utils", "inference"):
        _link(upstream / directory, out / directory)
    for directory in ("data/derived_data", "data/external_models",
                      "results/saved_models"):
        _link(upstream / directory, out / directory)
    (out / "data/nsd_data").mkdir(parents=True)
    for item in (upstream / "data/nsd_data").iterdir():
        if item.name != "fmri_v2.npz":
            _link(item, out / "data/nsd_data" / item.name)
    controlled = out / "data/nsd_data/fmri_v2.npz"
    np.savez_compressed(controlled, **arrays)
    (out / "run_brainit_seeded.py").write_text(SEED_WRAPPER)
    run_args = [str(seed), "--run_name", f"{condition}_s{subject_index}_seed{seed}"]
    run_args += ["--test"] if test else ["--subjects", str(subject_index)]
    metadata = {
        "schema": "brainit-input-control-v1",
        "condition": condition, "seed": seed, "subject_internal_zero_based": subject_index,
        "test_only_five_examples": test,
        "source_fmri_sha256": digest(source),
        "controlled_fmri_sha256": digest(controlled),
        "permutation_over_test_rows": permutation if condition == "deranged" else None,
        "condition_applied_to_actual_fmri": True,
        "npz_content_scope": "inference-only keys; original other keys untouched",
        "stimulus_row_order_verified_against_experiment_design": False,
        "model_inference_executed": False,
        "note": "Seed controls RNG only; PyTorch GPU operations may remain nondeterministic.",
        "shell_command_from_staged_root":
            "python run_brainit_seeded.py " + " ".join(run_args),
    }
    (out / "control_receipt.json").write_text(
        json.dumps(metadata, indent=2, sort_keys=True) + "\n")
    return metadata


def main(argv=None):
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--upstream", required=True, type=Path)
    ap.add_argument("--out", required=True, type=Path)
    ap.add_argument("--condition", choices=CONDITIONS, required=True)
    ap.add_argument("--subject-index", type=int, default=0,
                    help="0-based original author's subject-list index")
    ap.add_argument("--seed", type=int, default=20261024)
    ap.add_argument("--full", action="store_true",
                    help="Do not use upstream's first-five --test shortcut")
    args = ap.parse_args(argv)
    metadata = stage(args.upstream, args.out, args.condition, args.subject_index,
                     args.seed, test=not args.full)
    print(json.dumps({"staged": str(args.out), "command":
                      metadata["shell_command_from_staged_root"]}, indent=2))


if __name__ == "__main__":
    main()
