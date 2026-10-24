# Brain-IT scientific programme — research phases and deliverables

**Status:** Phase 0 substantially source-written; **Phase 1 (independent baseline) is the current scientific frontier**. 24 October 2026 (Brisbane).
**Owning PR:** [dashi_agda #1121](https://github.com/chboishabba/dashi_agda/pull/1121).
**Primary empirical/model authors:** Roman Beliy, Amit Zalcher, Jonathan Kogman, Navve Wasserman, Michal Irani, *Brain-IT: Image Reconstruction from fMRI via Brain-Interaction Transformer*, ICLR 2026; arXiv:2510.25976v2 (1 March 2026), https://arxiv.org/html/2510.25976v2.
**Reference implementation:** https://github.com/WeizmannVision/brainit-fmri.
**Dataset:** Natural Scenes Dataset (NSD; Allen et al., 2022), per-paper train/test protocol. Distinguish dataset provenance from the model's research claims.
**Scope:** computational neuroscience / machine learning / information retention / empirical scientific validation, *not* a claim of general thought reading, conscious-state decoding, or exact recovery of microscopic brain activity.

This is the **programme-level owner** for scientific milestones. The supporting document
[`Docs/BrainITDASHIBrainCMSRoadmap.md`](../BrainITDASHIBrainCMSRoadmap.md)
is an implementation and provenance ledger, not the project's strategic thesis.
Existing CMS/HEPData, Drosophila/connectome, generic coarse-fine theorem, and conscious-access modules are **optional method donors**, never prerequisites to constructing an independent human-fMRI benchmark or proving biological claims. Cross-project conceptual similarity cannot be promoted to same-object evidence.

## North-star research question

**Which stimulus-relevant properties are retained by brain measurements and learned functional clusters, how much reconstruction improvement comes from neural evidence rather than the generative image prior, and which representations generalise under limited subject-specific calibration?**

Three competing, falsifiable scientific hypotheses (not conclusions):

- **H1, functional sufficiency:** At matched compression level and inference/training budget, a learned functional-cluster representation preserves task-relevant predictive information better than random, anatomical, or spatial partitions on held-out subjects/stimuli.
- **H2, branch-disentangled information:** Semantic and low-level structural branches retain non-identical stimulus information. Their joint improvement should exceed well-chosen single-branch and prior-only controls; cross-attention by itself is not mechanistic evidence.
- **H3, transfer robustness:** Cross-subject sharing yields calibrated performance across subjects and recording budgets (15, 30, 60 minutes and full-data), beyond subject-specific memorisation or diffusion prior effects.

A null result or reversal under strong controls is a valid deliverable. Pre-register success criteria and metric directions before evaluation.

## Evidence/claim ladder

| Level | Evidence | Maximum allowed claim |
| --- | --- | --- |
| S0, typed architecture | Source-linked declarations and toy theorems | Formal interface or finite example exists |
| S1, verified formal lemma | Exact-head Agda kernel receipt and dependency inventory | Mathematical claim for the explicitly declared model |
| S2, published-value transcription | Tables from credited authors, linked to exact version | The original paper reports those numbers |
| S3, independent replay | Inputs and preprocessing/checkpoints/evaluator pinned, rerun logs and output digests | Reproduced (or failed to reproduce) a specified empirical benchmark |
| S4, controlled extension | Frozen matched baselines, seeds/splits, negative controls, uncertainty | A scoped empirical improvement or failure relative to controls |
| S5, held-out/causal support | Unseen stimuli/subjects or prospective interventions, independent replication | Qualified generalisation or specific mechanistic hypothesis support |

Never use S1 mathematical proof to promote an S2/S3 physical identification. Metric transcription in Agda is not independent evaluator execution.

## Phase and deliverable ledger

| Phase | Objective / output | Acceptance gate | Present state |
| --- | --- | --- | --- |
| **0 — Scope, formal baseline** | D0: source map, measured-vs-latent typing, collision/no-universal-inverse witness, paper metric fixtures, exact-head validation | Agda exact-head passes; no holes/unsound postulates in new path; Python static contract passes; exact source version/scope preserved | **Source-written / not kernel certified** |
| **1 — Independent benchmark** | D1: immutable experiment manifest, light inference/evaluator runner, per-subject outputs for baseline, reproducibility report and deviations | Specific released checkpoint + V2C mapping + NSD split + preprocessing + model/evaluator revisions + seeds + file hashes. Recompute table metrics from outputs, or report precise blockers; no table-as-computation shortcuts | **Not performed** |
| **2 — Neural evidence versus prior** | D2: blinded/counterfactual controls, semantic/structural branch measurements, quantitative evidence attribution and failure atlas | Identical image priors and decoding budgets for real fMRI vs shuffled/incorrect-subject/no-signal conditions; report per-stimulus, per-subject and uncertainty; check for data leakage | **Unstarted** |
| **3 — Representation and compression** | D3: functional V2C vs spatial/anatomical/random/matched-capacity and optional locality/spectral quotients; information/commutation diagnostics where well-defined | Hold training, splits, cluster count and inference compute comparable; report CLIP/structure/fidelity metrics separately, with sampling error and negative results. No assumption anatomical connectome == learned functional clusters | **Proposed / no NSD test** |
| **4 — Calibrated transfer and OOD** | D4: calibration-cost/performance curves, held-out subject/stimulus and OOD stress tests, robustness audit | Frozen participant exclusions, 15/30/60-min and full-data budgets, unseen stimuli; report domain-shift failures and confidence intervals; no claimed beyond-protocol generality | **Proposed** |
| **5 — New research method** | D5: optional original model/projection/intervention from phases 2–4 that yields a testable advance | Demonstrate statistically supported gain, calibration efficiency, robustness, or a useful negative theoretical boundary over strong matched baselines; include compute cost | **Decision-gated** |
| **6 — Communicable scientific output** | D6: reproducibility artifact, clearly attributed methods/results report, optional paper or technical note | Independent replay and core controls; clear original versus published contributions, limitations, data/software rights and reproducibility appendix | **Not publication-ready** |

## Highest-value next cut: D1 rather than another abstract theorem

The authors publish an inference-first route: `./data/scripts/run_all_downloads --inference-only`,
`./data/scripts/run_all_data_processing --inference-only`,
`python data/scripts/download/download_checkpoints.py`, and
`python inference/full_inference.py`. Stage-2 *training* is documented as requiring 2×H200 or 4×H100 GPUs; do not equate that with inference requirements. Avoid a forced retraining plan until inference and evaluator cost is scoped.

D1 must deliver:
1. **Artifact inventory:** git revision and content hashes for model weights, voxel-to-cluster mapping (`v2c_128_mapping_gmm_v2.npy`), reference preprocessing, and versioned NSD imagery/fMRI and ROI selections. Record data rights and access constraints. Any unavailable hash or data file remains `missing`, not a guessed receipt.
2. **Evaluation contract:** the paper's shared-image test protocol and Subjects 1,2,5,7 mean vs Subject 1 transfer; explicit definitions of PixCorr, SSIM, CLIP identification and additional non-saturating metrics (e.g. LPIPS/1000-way CLIP) where supported; repetition policy, number of images, pairing, pretrained-prior leakage checks, test seeds.
3. **Small, independent replay:** run the released inference and evaluation on an agreed bounded sample; preserve model/data/evaluator IDs, stimulus indices, per-image outputs, metric vectors and exact command log. Start with existing checkpoints, not new training.
4. **Decision review:** if baseline cannot be reproduced, classify as rights/access, missing resources, missing evaluator, algorithmic mismatch, or numerical stochastic variance, with a concrete minimal next action. Do **not** proceed to original-model leaderboard claims.

## D2/D3: discriminating analyses that could support an original result

A. **What does fMRI add?** Compare correctly paired fMRI to shuffled pairings, wrong-subject samples, zero/constant-input and prior-only image generation; hold diffusion seeds/prompts/budget fixed and avoid leaking ground truth through preprocessing. Use a matched, preregistered evaluation. Document semantic correctness versus image layout and hallucination rate. Do not treat high visual realism as proof of neural information recovery.

B. **What is retained?** Separate *stimulus discrimination* and *microscopic-state reconstruction*. For `Q : neural state -> measured observation` and `T : neural state -> declared consumer`, a collision can refute an exact decoder of T from Q for the specified model. Approximate reconstruction and statistical generalisation require data, calibration and uncertainty; exact factorisation cannot be inferred from visual similarity.

C. **Which quotient matters?** Compare clustering methods at fixed capacity/data/compute, including token permutations, random assignments, anatomy and data-driven function. Ablate 8/16/32/64/128/256/512 token budgets in step with paper Table T3. Test stability across subjects and preprocessing. Any optional DASHI spectral/locality method is an **additional ablation**, not the default scientific hypothesis.

D. **Brain-IT-vs-baseline caution:** In the original paper T2, 3D-coordinate clustering has higher SSIM (0.491) than functional clustering (0.486), while functional has better PixCorr (0.386 vs 0.378); do not collapse multiple task metrics into a single victory. Paper T3 labels 128 as a tunable hyperparameter. The authors' own branch ablation (paper Table 2) supports studying low-level and high-level information separately.

## Decision gates and resource-aware execution

- **G0 (formal hygiene):** certify exact head of D0, or clearly keep it draft; this is *not* the blocker for preparing D1 manifests.
- **G1 (baseline feasible):** accessible data rights, realistic compute/memory, runnable pretrained inference and evaluator on a bounded sample. If GPU constraints preclude generation, start from available saved reconstructions / deterministic feature-level or evaluator-only reproduction with explicit lesser status.
- **G2 (novelty):** at least one D2/D3 comparison yields a reproducible, nontrivial difference after prior/seed/split controls; or a clearly interpretable negative result.
- **G3 (method development):** invest in a novel projection/architecture only when its predicted advantage follows from G2 and can be falsified at reasonable cost.
- **G4 (publication):** source-authored discoveries and external authorship separated; full data/model version log and uncertainty.

**Stop/defer:** generic CMS formalisation, new Drosophila fMRI identity, unsupported consciousness/DMT bridges, exact-128 metaphysics, full heavyweight retraining, and speculative mechanism claims based solely on attention visualisations. Revisit only for a concrete measured consumer.

## Deliverable priorities for the immediate research cycle

1. D0 certification cut on the existing branch; no new ontology unless compilation actually requires it.
2. D1 artifact manifest and evaluator contract **in parallel**; this is the highest-alpha unblocked scientific task.
3. Bounded inference/evaluator pilot, including at least one real-fMRI vs shuffled-input comparison.
4. Pre-registered D2/D3 ablation matrix and error atlas based on the pilot; then make the go/no-go decision for an original model.

The next milestone is **not** "prove Brain-IT" or "extend CMS": it is an independently reproducible, stimulus-level Brain-IT baseline with adequate controls and an honest decomposition of neural evidence versus generative prior.