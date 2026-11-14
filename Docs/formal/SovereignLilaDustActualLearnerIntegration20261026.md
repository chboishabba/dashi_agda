# Real Sovereign-LILA/E8GPT → Dust integration: concrete source audit (2026-10-26)

## Source and actual learner identity
**Upstream:** [SPUTNIKAI/sovereign-lila-e8](https://github.com/SPUTNIKAI/sovereign-lila-e8), accessible through [meta-introspector/sovereign-lila-e8](https://github.com/meta-introspector/sovereign-lila-e8), with upstream architecture and model-specific claims retaining their authorship and attribution. **DASHI/DASHIg:** separate engineering/formal audits; mirrored source is not automatically owned by DASHI. **Dust:** Samip Dahal, Bishwas Mandal, Serdar Gülbahar, Akshay Vegesna, https://qlabs.sh/research/dust/ and https://github.com/qlabs-eng/dust. Avoid merging upstream authorship across projects.

Confirmed in the accessible Sovereign-LILA source:
- `scripts/train_model.py` dispatches `training/train.py:train`.
- `training/train.py` instantiates `models.model.E8GPT(cfg)` and runs AdamW(5e-5), `loss.backward()`, clip_grad_norm_(1.0), and `optimizer.step()` on streaming batches.
- `models/model.py` defines `E8Quantizer` (straight-through), `E8Attention` (qkv, E8 head directions/scales), `E8TransformerLayer` (to_e8, from_e8, E8 scale and FFN), `E8GPT` and `E8GraphResonator`.
- `E8TransformerLayer.forward` itself injects multiplicative/random additive noise in training mode. Controlled Dust probes need paired common random numbers or ability to disable this native randomness; otherwise covariance credit is confounded.
- `E8GraphResonator.encode_relation` mutates memory under no_grad; any paired perturbation experiment must snapshot/reset that memory to compare like with like.

**DASHIg** canonical study repo has existing real `phase2_validation/leech_modular_benchmark.py` (a separate Leech modular-classifier comparison), plus LILA external log adapters `35_lila_log_to_csv.py`, `36_lila_training_dynamics.py`, `37_lila_delta_cone_analysis.py`, and `38_lila_phase2_pipeline.sh`. `DASHI/Physics/Closure/SiblingEvidenceInventory.agda` refers to `../DASHIg/LeechTransformer/vocab/e8_morpheme_.model`, a Leech/E8 vocabulary pointer. The GitHub repository content endpoint did not expose `LeechTransformer/models/model.py` or `LeechTransformer/training/train.py` as ordinary tracked files. Therefore **do not claim full Sovereign-LILA source is vendored there** merely from the path notation.

## Exact insertion strategy
At `E8TransformerLayer` residual `from_e8(res_feat)` first, add activation-noise instrumentation around the output of the fixed source layer (no parameter mutation between population probes). One forward baseline and K perturbed forwards over the same input, data order, dropout/random states and model memory; build per-token CE and future-token credit using the paper's *population-mean perturbed-loss centering*. Use the true inputs to the immediately upstream trainable projection for the outer product, and update specifically that projection's weight with the correct sign and reduction scaling. This should first be a **restricted targeted projection update**, not a claim that the entire 40M parameter model has become forward-only trained.

Once shape and layer correspondence is demonstrated, extend to attention output/head and residual scalars following Dust's distinct estimator paths; only after this can one fairly compare whole-model Dust training against AdamW.

## Match/acceptance gates
1. Source-pinned model SHA and Dust SHA, check code/license boundaries and checkpoint metadata before copying.
2. Exact patch against E8GPT at a concrete layer, preserving baseline checkpoint compatibility.
3. Fixed, matched batches, model train/eval flags, dropout mask and random draws; distinguish existing LILA forward randomness from experimental noise.
4. Test `loss_before`, `loss_after`, gradient/credit norms, E8 roots and geometry, whether layer updates actually occur, and state restoration after unsuccessful trials.
5. Benchmark quality as validation NLL, plus E8 geometry / long-context ablations, walltime, joules, memory and all K forward passes. Include AdamW and noise-only controls.
6. Attribution receipts: original authors, fork/submodule/mirror relation and modification ownership; never infer E8 physics or consciousness from architecture name or language generation.

## Current boundary
This is an inspected source-specific *integration route* to real `E8GPT`, not an executed Sovereign-LILA training trial. The existing toy finite optimizer in this PR does not satisfy the whole-model implementation gate. CI remains out of scope.


## Parallel-worker handoff: exact probe isolation producer, 26 October

Added `DASHI/Reasoning/LILADustProbeIsolationExact.agda` on the Dust/Noise branch, without changing the original LILA implementation or its future PR. Its `ForwardProbeExperiment` requires both clean and perturbed forward evaluations to be related to the **same parameter value, input, random-state and pre-measurement memory state**. This is an eligibility contract, not proof that E8GPT actually restores RNG or its resonator state. The two-state finite counterfixture shows that differing RNG states can alter readout even without any intended intervention.

Next step when the parallel LILA worker lands: use exact branch/commit of their actual E8GPT patch; connect the true runtime RNG/memory capture-and-restore operations to this contract, then record measured forward deltas, trainable layer weight updates and held-out paired accuracy. Do not conflate the current `training/train.py` AdamW/backprop baseline with a newly proven forward-only learner. This module is source-written, kernel-unverified; CI intentionally skipped.
