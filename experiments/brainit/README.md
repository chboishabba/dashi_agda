# Brain-IT: reproducible scientific experiment harness

**Primary study:** Beliy, Zalcher, Kogman, Wasserman, Irani, *Brain-IT: Image Reconstruction from fMRI via Brain-Interaction Transformer*, ICLR 2026, [arXiv:2510.25976v2](https://arxiv.org/html/2510.25976v2).
**Original code:** [WeizmannVision/brainit-fmri](https://github.com/WeizmannVision/brainit-fmri), inspected at commit `a7663eb5002e9ea5f899815326ff52d45be9a2f3` (2026-10-17). **Original released weights:** RomanBeliy/Brain-IT at Hugging Face. The external code, study, checkpoint and dataset remain credited to their creators.

This directory is a **new, independent evaluation and ablation harness**. It does not vendor, fork or claim authorship of the Brain-IT model. It is runnable with local Python and the authors' separately installed/rights-approved data. **No actual checkpoint inference, NSD evaluation, or new performance results were executed in the code-authoring session.**

## Core dependencies and interpretation

Lightweight audit/evaluation: `numpy`, `scipy`, `scikit-image`, `pytest`. External inference additionally requires the authors' documented `brain-it` environment, model checkpoints, raw/processed NSD data, and GPU (the upstream `full_inference.py` explicitly invokes `.cuda()`).

This is not a standalone Brain-IT reimplementation: `stage_conditions.py` symlinks the upstream source and weights read-only and writes a **separate** `data/nsd_data/fmri_v2.npz` in the staged directory. It never overwrites original fMRI or model weights. The derived NPZ contains only `multi_sub_fmri`, `num_voxels_subjects`, and `type_sample`: the three numeric fields used by the official inference loader. No pickled `type_desc` or unused enormous single-subject array is loaded into memory. Staged outputs are written into the isolated `results/reconstructions` directory.

### D1 — Actual identity and source pairing

The **first** admission test must establish that a human fMRI trial row and the original image refer to one same stimulus. The upstream `prepare_fmri.py` uses `subjectim[0][:1000]` to order shared fMRI rows; `full_inference.py` builds ground truth via sorted `type_sample == 2`. Equality of these orders is **not proven by source code**. `alignment.py` resolves the permutation using the original `experiment/nsd_expdesign.mat`. If source image sets disagree, the run **fails closed**. If the sets agree but order differs, the independent evaluator uses original row identities; the upstream printed metrics need explicit review.

```sh
UPSTREAM=/path/to/brainit-fmri
python experiments/brainit/alignment.py \
  --fmri "$UPSTREAM/data/nsd_data/fmri_v2.npz" \
  --design "$UPSTREAM/data/nsd_data/experiment/nsd_expdesign.mat" \
  --out /path/to/receipts/alignment.json

python experiments/brainit/inventory.py \
  --upstream "$UPSTREAM" \
  --fmri "$UPSTREAM/data/nsd_data/fmri_v2.npz" \
  --images "$UPSTREAM/data/nsd_data/nsd_images_224.npy" \
  --design "$UPSTREAM/data/nsd_data/experiment/nsd_expdesign.mat" \
  --mapping "$UPSTREAM/data/derived_data/v2c_128_mapping_gmm_v2.npy" \
  --checkpoint "$UPSTREAM/results/saved_models/combined_model.ckpt" \
  --checkpoint "$UPSTREAM/results/saved_models/decoder_vgg_ext-1_batch64_save.pth" \
  --checkpoint "$UPSTREAM/results/saved_models/decoder_clipg_ext-1_save.pth" \
  --out /path/to/receipts/inventory.json
```

All input/checkpoint hashes are measured from local file bytes. A complete inventory is only `artifact_inventory_complete_not_replayed`: it is not an executed reconstruction receipt. The actual upstream git revision and dirty state are separately recorded; choose and freeze a revision **before** running the benchmark.

### D2 — Paired fMRI versus actual-input controls

Stage each condition into its own new directory (all are derived from the **same** original fMRI):

```sh
python experiments/brainit/stage_conditions.py --upstream "$UPSTREAM" \
  --out /path/to/brainit-runs/paired --condition paired --seed 20261024
python experiments/brainit/stage_conditions.py --upstream "$UPSTREAM" \
  --out /path/to/brainit-runs/deranged --condition deranged --seed 20261024
python experiments/brainit/stage_conditions.py --upstream "$UPSTREAM" \
  --out /path/to/brainit-runs/zero --condition zero --seed 20261024
```

From each staged directory run the `shell_command_from_staged_root` in `control_receipt.json`. For example, from `paired/`:

```sh
python run_brainit_seeded.py 20261024 --run_name paired_s0_seed20261024 --test
```

The official `--test` option is **five examples, internal subject 0 (NSD Subject 1)**. For other original subject indices 1..7 use `--full --subject-index <0..7>`; the script then emits `--subjects INDEX`. This is **not** the held-out `--transfer` training/evaluation protocol. Those records must be kept separate until calibrated transfer checkpoints are available.

`deranged` reassigns within-subject test fMRI rows via a seeded, no-fixed-point permutation, preserving voxel dimensions and all other subjects; `zero` sets only the tested subject's measured matrix block to zero and is an out-of-distribution stress test. Both retain original image labels. Holding the upstream random seed fixed reduces RNG confounding but cannot guarantee deterministic CUDA kernels, nor rule out generative-prior behaviour. No claims about mind reading or causal neural necessity follow from these controls alone.

### D1/D2 — Independently scored reconstructions

Use the generated `.../subject_0/enhanced_recons.npy` or `low_level_recons.npy` / `semantic_recons.npy` files. **Score against source images and the original NSD experiment design** (the staged numeric NPZ is valid because `type_sample` is preserved).

```sh
python experiments/brainit/evaluate.py \
  --recons /path/to/brainit-runs/paired/results/reconstructions/paired_s0_seed20261024/subject_0/enhanced_recons.npy \
  --images "$UPSTREAM/data/nsd_data/nsd_images_224.npy" \
  --fmri "$UPSTREAM/data/nsd_data/fmri_v2.npz" \
  --design "$UPSTREAM/data/nsd_data/experiment/nsd_expdesign.mat" \
  --subject 1 --condition paired --seed 20261024 --branch enhanced \
  --out /path/to/receipts/paired.json
```

Repeat for deranged and zero with corresponding output paths and condition flags. Compute paired condition contrasts:

```sh
python experiments/brainit/compare.py \
  --paired /path/to/receipts/paired.json \
  --control /path/to/receipts/deranged.json \
  --seed 20261024 --draws 2000 --out /path/to/receipts/contrast.json
```

The evaluator computes mean per-image pixel correlation and grayscale gaussian-weighted SSIM after independent 425×425 interpolation. The original paper's metric code uses `torchvision` and additional CLIP/AlexNet/LPIPS models; this lightweight calculation is **not claimed bit-identical to the published tables**. The optional `--feature-gt`, `--feature-recons`, `--feature-source` path computes an explicitly labeled N-candidate two-way identification rate; it must **not** be relabeled as published 1000-way CLIP. A real full benchmark needs the original candidate-pool and encoder/distractor implementation.

The paired contrast compares *the same* stimulus, subject, branch and seed; it refuses missing or duplicated pairs and mismatched original image source hashes. Bootstrap intervals resample **the measured stimuli of the observed subjects**; they are not confidence intervals on the population of all humans. Raw arrays and source identifiers must remain accessible to reproduce each point.

### D3 — Capacity-matched information retention, not a V2C model claim

`probe.py` accepts explicitly split `train-x.npy`, `test-x.npy` (fMRI voxel matrices), `train-y.npy`, `test-y.npy` (frozen target feature vectors), a one-integer-per-voxel cluster-label vector, and unique train/test stimulus-ID JSON arrays. It performs train-only centering/standardisation and a ridge linear probe after per-cluster *mean pooling*. For random controls, it shuffles the voxel assignments while preserving **exact cluster sizes**.

```sh
python experiments/brainit/probe.py \
  --train-x train_x.npy --test-x test_x.npy \
  --train-y train_y.npy --test-y test_y.npy \
  --labels cluster_labels.npy --train-ids train_ids.json --test-ids test_ids.json \
  --source-of-visual-features "named encoder, version/hash" \
  --partition-provenance "named cluster method and source" \
  --out /path/to/receipts/probe.json
```

This deliberately does **not** identify its mean-pool ridge model with Brain-IT's weighted V2C or interaction transformer. It tests a narrower scientific property: held-out linear recoverability at a given compression budget. Direct Brain-IT V2C replacement is deferred until official checkpoint-compatible mapping semantics are verified.

### D4 — Transfer generalisation

`transfer.py` consumes a JSON array of `{"minutes":15,"evaluation":"/.../receipt.json","checkpoint_sha256":"<actual lowercase SHA-256>"}` entries. It refuses mismatched subjects, stimuli, seeds and evaluation implementations. It does **not** derive held-out-subject data from five-sample full-data runs. Independent 15/30/60-minute transfer requires the separately documented `train_transfer/README.md` protocol and actual adapted checkpoint hashes.

### Verification and promotion gates

```sh
python -m pytest -q tests/test_brainit_experimental_harness.py tests/test_brainit_probe_transfer.py
python -m pytest -q tests/test_brainit_fmri_maxcut.py tests/test_brainit_connectome_weld.py tests/test_brainit_consumer_receipts.py
agda -i . DASHI/Biology/BrainITValidation.agda
```

The first two commands are source-authored tests; **their presence does not constitute a passing runtime receipt**. Agda and actual inference must be run in the correct environment before any claim of certification. No CI requirements are imposed on this cut.

## Explicit unresolved scientific costs

1. **D1**: actual NSD design and arrays, rights review, model/checkpoint availability and hashes, alignment, independent evaluator and matched replay versus paper's own scripts.
2. **D2**: run genuine paired/deranged/zero cases through original model on identical held-out stimuli and seeds. Quantify dependence on neural evidence, distinguish prior-only plausibility from representational fidelity, and audit input-vs-label leakage.
3. **D3**: train/test fMRI plus separately sourced visual feature vectors; matched-capacity random/anatomical/functional probes; determine if a full Brain-IT-compatible projector test is justified.
4. **D4**: actual independent transfer checkpoints and uncertainty across subjects. No universal subject-generalisation assertion from a single subject.
5. **D5/D6**: only pursue new model/paper claims after measured limitations and independent control evidence. Failure and null-result cases are valid research outputs.

For scientific priorities and go/no-go decisions see [BrainITScientificProgramme.md](../../Docs/roadmaps/BrainITScientificProgramme.md). CMS and dashiBRAIN are *not* required for this human-fMRI study.
