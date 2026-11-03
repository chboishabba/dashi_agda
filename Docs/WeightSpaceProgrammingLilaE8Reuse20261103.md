# WSP × Sovereign-LILA/E8GPT × Dust × Leech: exact reuse and discriminator cut

**Date:** 2026-11-03. Companion to [WSP PR #1463](https://github.com/chboishabba/dashi_agda/pull/1463). This is a **source-aware plan and finite theorem bridge**, not an executed checkpoint repair.

## Inspected sources and attribution

**MIT CSAIL (external):** Rikiya Takehi, Jayden Teoh, Alex Zhang and Omar Khattab, *Sparks of Weight-Space Programming*, 2026-11-02, logs `RikiyaT/lm_understand-logs@4d09ba6d6a7e891dd8063974dfe81b3d78e3494f`. The relevant Qwen3.5-0.8B run is `exp8_math/runs/p50c`, changing 64 MLP down-projection columns each at layers 15 and 19, not training with an optimizer. See `Docs/WeightSpaceProgrammingDASHIPriorArtMaxCut20261103.md`.

**Original E8GPT engineer/project:** `SPUTNIKAI/sovereign-lila-e8`; current accessible mirror `meta-introspector/sovereign-lila-e8`. Source inspected: `models/model.py` and `training/train.py`. The upstream initial model training is **AdamW with backward**, not a forward-only learner by default. `E8Quantizer` normalizes 240 E8 roots and uses a temperature-softmax over squared distances, with a straight-through expression `x + (quantized - x).detach()`. `jit_e8_attention_bias` constructs a per-head rank-one dot-product bias using 8D projected Q and K and a head-scale parameter. `E8GraphResonator` has mutable memory. Distinguish these mechanisms.

**DASHI prior owners (open branches):**
- [#1094](https://github.com/chboishabba/dashi_agda/pull/1094) `DASHI.Reasoning.SemanticInterventionEquivarianceExact`: source-written labelled/invariant/structural intervention actions, representation/decoder commutation, and non-promotion to mechanism.
- [#1095](https://github.com/chboishabba/dashi_agda/pull/1095) `DASHI.Cognition.Teleodynamics.{GeometricLearnerPriorExact,LilaE8QuantizerExact,LilaE8AttentionBiasExact,LilaOrthogonalAttentionExact,LilaGeometricRegularizerExact}`. These have separate ablations; the 240 root chart and Q/K shared orthogonal gauge do not prove actual weight repair.
- [#1265](https://github.com/chboishabba/dashi_agda/pull/1265) `DASHI.Reasoning.{LILAForwardOnlyDustAdapterExact,LILADustProbeIsolationExact}`, `scripts/sovereign_lila_dust_projection_step.py`, `scripts/run_sovereign_lila_e8_dust_smoke.py`. Original Dust: Samip Dahal, Bishwas Mandal, Serdar Gülbahar and Akshay Vegesna. The code addresses `E8GPT.core.layers[-1].from_e8.weight` by population-centred *forward activation noise credit*, not the Qwen p50c mask/projection. PR #1265's reported executed CE change 2.3726654→2.3514826 is for a PyTorch shape-compatible local analogue; original upstream E8GPT execution/checkpoint is not paid.
- [#1442](https://github.com/chboishabba/dashi_agda/pull/1442) and [LeechTransformer #4](https://github.com/chboishabba/LeechTransformer/pull/4): history-bearing MoE, geometric priors, exact finite C2/C3 transport/quotient contracts; Anatolii Kornienko retains Leech-LILA attribution. Per-expert history equivariance does not itself supply shared canonical history or test-time quality.
- Native default-branch `DASHI.Algebra.Trit.E8RootEnumeration` and `DASHI.Physics.Closure.LilaE8RootEnumerationNoDuplicatesSurface`: indexed length 240 and executable no-duplicate/disjointness checks; upstream native E8 completion receipt remains separated from these finite checks.
- `DASHI.Physics.Closure.LilaE8InitialisationPriorNote` explicitly distinguishes the SPUTNIKAI engineering project from unrelated AllenAI Lila benchmark and excludes external engineering-to-physics promotion.
- **Lean follows Agda:** [dashi_lean4 #43](https://github.com/chboishabba/dashi_lean4/pull/43) mirrors semantic-intervention/decoder equivariance and explicitly requires a genuine 240-root/action bridge; [#44](https://github.com/chboishabba/dashi_lean4/pull/44) adds geometric/finite E8 and E6 action tests, but explicitly leaves empirical LILA trajectories and held-out intervention receipts open. Both are source-written/kernel-unverified on the inspected PRs. No separate Lean definition is introduced in WSP #1463.
- [#1456](https://github.com/chboishabba/dashi_agda/pull/1456): Divyansh Agrawal's original Qwenputer is a **separate** Qwen/GDN/RV32 architecture with its own fidelity obligations. No architecture identity with this Qwen3.5-0.8B experiment.
 
## What can actually compose

| Intervention | Exact targeted surface | Intended effect | Distinguishing control |
|---|---|---|---|
| MIT p50c WSP | Qwen MLP `down_proj` columns (two layers) | Reduce repetitive-generating direction | matched random-direction/norm and no-op |
| LILA E8 soft quantizer | 8D hidden chart and root-average readout | representation restriction | quantizer on/off with all else fixed |
| LILA E8 attention bias | additive per-head rank-one attention-logit term | change attention selection | head scale zero/nonzero with quantizer fixed |
| LILA shared orthogonal Q/K | both Q/K under same orthogonal transform | score-preserving coordinate gauge in exact algebra | identical score; **not** a repair by itself |
| Dust LILA projection update | final `from_e8.weight` | forward-only loss-directed training step | AdamW, ordinary zeroth-order, orthogonal probes, no-op |
| Leech/MoE historical transform | expert activation/history with revision | route/transport/compress shared state | same checkpoint, identical histories, byte-exact reconstruction |

In the original E8 quantizer model, `z \mapsto \sum_{r\in R_{E8}} \operatorname{softmax}(-\|z-r\|^2/\tau)_r r` is a **forward semantic map**; the straight-through derivative is a separately chosen optimisation surrogate. Qwen WSP's column rewrite does not automatically commute with this quantizer or share its loss geometry.

The E8 bias term has rank-one **feature geometry**: \(\beta_h\langle q_8,r_h\rangle\langle k_8,r_h\rangle\). That does not prove a rank-one **parameter rewrite** equals MIT's patch. A shared orthogonal Q/K transformation satisfies \((QO)(KO)^\top=QK^\top\) in exact arithmetic when \(OO^\top=I\); hence a pure shared gauge is an especially important negative control. Floating point and nonorthogonal implementations require separate analyses.

## New standalone Agda owner

`DASHI/Reasoning/WeightSpaceProgrammingLilaE8InterventionExact.agda` imports only the existing WSP finite `--safe` owner and models independent local parameter-projection, attention, codebook, quantizer and resonator-memory **state coordinates**. Source-written theorems cover:
- projected direction removal under a selected mask;
- non-target quantizer/codebook/memory state preservation;
- attention-only edits not rewriting the quantizer coordinate;
- idempotence of the declared projection patch;
- explicit no-promotion constructors for held-out gain, inferred E8 mechanism, conflating Dust with WSP, or claiming an orthogonal shared gauge changes score.

These are disjoint-state invariants in a synthetic carrier. The real E8 quantizer output can change because inputs to it change, even when its parameter/state coordinate is untouched. There is **no** implied full-program noninterference, real tensor fit, E8 group action, or kernel acceptance.

PRs #1094/#1095/#1265 are not on the same default-branch head as WSP #1463. Do not directly import missing files or copy their definitions: merge/rebase their actual owners and then create a typed same-object bridge, or consume them with explicit pinned branch dependency. This new standalone module is only a proof-conservative adapter until that happens.

## Critical high-alpha test: reuse the E8 prior for WSP search

**New proposal, not demonstrated:** define a root-aligned intervention dictionary on a *validated* eight-dimensional hidden chart. Lift each of the 240 verified root directions through a checkpoint-specific hidden/parameter Jacobian or explicitly measured activation map into candidate parameter edits. Compare such directions against arbitrary equal-norm random directions and MIT-style discovered directions.

The E8 root set does not live automatically in 1,024-dimensional Qwen MLP output coordinates or an entire 40M-parameter E8GPT model. An explicit map \(J : \mathbb R^8 \to T_W\mathcal W\) and source-calibrated objective is necessary. If \(J\) is noninjective or poorly conditioned, distinct roots can yield indistinguishable or near-zero weight edits. Quantization can then erase an intended intervention, as in 884 BF16 roundbacks of the p50c addressed entries.

### Same-object experimental factorial grid

- **Model A:** reproduce exact Qwen3.5-0.8B base/p50c checkpoint and evaluation before generalizing.
- **Model B:** actual Sovereign-LILA `E8GPT` checkpoint, native quantizer, attention bias and final projection; compare WSP-like direct patch, Dust forward-only step, random equal-budget edits, AdamW updates and no-op. Freeze RNG/dropout and `E8GraphResonator` state across matched probes.
- **Model C:** Leech/MoE strict and hybrid learners with the observed CE gap; disentangle missing representation capacity, routing/history access and removable interference, with equal parameter budgets and held-out test data. Changing model family invalidates the assumption that Qwen's discovered direction transfers.

Readouts: held-out CE/accuracy, generation loops, truncation rate, calibration, geometric alignment, variance across seeds, exactly changed BF16 values, walltime/energy, and candidate-search/forward-pass budget. No claim that all performance changes derive from one cause without controls.

### Exact remaining obligations

1. **L8-W01:** pin source revisions and exact executable E8GPT checkpoint, record weights and both RNG and resonator memory restoration.
2. **L8-W02:** import the already-existing native 240-root source owner through an *actual agreed branch*, prove selected eight-dimensional chart/same-root action and validated hidden-to-parameter lift (including bitcast/rounding).
3. **L8-W03:** define and prove composition laws for `patch projection`, `toggle attention bias` and `toggle quantizer`, including identifying which pairs do not commute on the real model.
4. **L8-W04:** source-refine the actual Dust estimator/outer-product update and verify same-state paired probes, estimator sign, causal reward normalization and checkpoint mutation.
5. **L8-W05:** run matched capacity/interference/accessibility controls across Qwen, E8GPT and C2/Leech; reject E8 geometric benefit if random or zero-scale baselines explain it.
6. **L8-W06:** attach the proven artifact hashes, held-out receipts and source heads to Agda theorem/consumer boundaries; keep physical/VOA and semantic-action promotion explicitly separate.

**Status:** newly source-written finite Agda bridge; kernel not executed; no actual E8GPT checkpoint experiment, downstream score identity or real trained-model replication. No ESD edits.
