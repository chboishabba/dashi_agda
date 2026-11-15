# Weight-Space Programming × DASHI — source-pinned prior art and exact max-cut

Date: 2026-11-03. Golden root: `DASHI/Reasoning/WeightSpaceProgrammingInterventionExact.agda` (`{-# OPTIONS --safe #-}`). Legacy-owner adapter: `DASHI/Reasoning/WeightSpaceProgrammingOwnerBridgeExact.agda` (deliberately non-golden because pre-existing compression/realization imports are not all safe-qualified). Both are included by `DASHI.Reasoning.Everything`. This is a source-written independent finite abstraction, **not** a kernel-accepted real Qwen proof.

## Primary attribution and evidence

- **External original:** Rikiya Takehi, Jayden Teoh, Alex Zhang, Omar Khattab (MIT CSAIL), *Sparks of Weight-Space Programming: LLMs can natively read & write neural network weights*, 2 Nov 2026, https://rikiyat.github.io/blog/weight-space-programming/ . Credit the authors for the name, conceptual finding, diagnostic and intervention.
- **Reproducibility receipts:** pinned external logs commit `4d09ba6d6a7e891dd8063974dfe81b3d78e3494f`; https://github.com/RikiyaT/lm_understand-logs/tree/main/exp8_math , specifically `README.md`, `runs/p50c/final_answer.md`, `runs/p50c/edit/manifest.json`, `runs/p50c/work_notes/frozen_weights_manifest.json`, `code/apply_edit.py` and `eval/{unedited,p50c}/merged.json`. Third-party benchmark licensing applies; logs and model data are CC BY 4.0, scripts MIT.
- **Edited checkpoint:** Qwen/Qwen3.5-0.8B public text checkpoint at base revision `2fc06364715b967f1860aea9cf38778875588b17`. No DASHI work on Qwen weights has been run by this tranche.
- **Architectural prior:** Divyansh Agrawal, *Qwenputer*, 22 Oct 2026, https://github.com/divagr18/qwenputer; prior formal DASHI work in PR #1456. That project and this weight-editing experiment are **distinct** and should not be conflated.

## Specific published experiment (exp8/p50c)

- Qwen3.5-0.8B, thinking enabled, 24 layers. The agent could inspect CPU-loaded tensors and request at most 50 forward passes on practice data; it had no autograd, optimizer, backpropagation, training loop or access to held-out benchmark evaluations. One forward request could contain many sequences. The model did **not** infer the Qwen fix from static raw tensor text alone.
- Patch: `model.language_model.layers.15.mlp.down_proj.weight` and `model.language_model.layers.19.mlp.down_proj.weight`, each shape `[1024,3584]`, each with 64 selected input columns. 2 × 1024 × 64 = **131,072 addressed scalar entries**, about 0.016% of 800 million. After BF16 rounding **65,260 + 64,928 = 130,188 entries actually changed**; 884 touched entries rounded to the original bit pattern. Do not identify 'addressed' with 'numerically changed'.
- Reported held-out evaluation under the specified sampling and prompt protocol: MATH-500 7.9%→48.1%, GSM8K 13.8%→67.1%, IFEval 21.0%→62.3%, MATH-500 truncation at 32,768 tokens 93.0%→33.1%. These are *the authors' measurements*, not kernel proofs, benchmark replications here, or demonstrated new mathematical knowledge.
- Source-specific intermediate history: the 10-pass edit touched 30 matrices with a rank-one-like direction modification, whereas the 25-pass run switched off layer 15 attention head 7, and the 50-pass run selected the 2 MLP tensors. They are not one monotonic optimizer trajectory, and 10/25 edits must not be retroactively interpreted as the final 50-pass patch.
- The final-answer report mentions paired 1,152 practice problems and norm-matched random controls, but practice data are not the unseen benchmarks. The actual non-linearity, attention, decoding and token-limit effects must not be deduced from our two-axis toy model.
- Negative control: their Gemma 3 270M MATH-500 experiment did not show a comparably useful gain in a non-looping model; the repair-vs-knowledge distinction must stay open.

## Existing DASHI owners — reuse, not reinvention

| Owner | What transfers | What does not |
|---|---|---|
| `DASHI.Reasoning.RelationRepresentationRealizationExact` | Realization witness and compression-collision non-promotion | Identification of Qwen's latent mechanism |
| `DASHI.Reasoning.StructuralMetaphorTaskCompressionExact` | Consumer-relative information preservation | Downstream task success from one stable channel |
| `DASHI.Reasoning.FibreRoutingGrokkingMoEBrainCrossPollinationExact` | Routed/localized fibre grammar, overlap and selected submodules | A MoE expert or Fly fibre as the Qwen MLP direction |
| `DASHI.Reasoning.FibreRoutingDistillationCompressionCrossPollinationExact` | Pruning/low-rank/quantization adequacy boundaries | An inference that any sparse weight modification is a compression success |
| `DASHI.Core.AdaptiveMechanismDiscriminationPlannerExact` | Residual-conditioned controls and decision-specific closure | Unique causal localization from static weights alone |
| Agda PR #900 | Frozen candidate -> intervention -> held-out test discipline | Automatic transplant of Mod97 circuitry to Qwen3.5 |
| Agda PR #1442 (LeechTransformer PR #4 companion) | Expert-history revision, signed interventions and federated admission | Same-object PyTorch/cryptographic transport proof |
| Agda PR #1456 | Qwenputer Gated DeltaNet/RV32 binary–ternary architecture | The 24-layer Qwen checkpoint's actual MLP surgery |
| Agda PR #1265 | Dust forward-only perturbation and paired controls | Gradient-free direct editing being identical to Dust |

## Formal target

For checkpoint parameters \(W\), an allowed coordinate mask \(M\), and a proposed local rewrite \(T\), define coordinatewise \(W'_{\ell,j}=T(W_{\ell,j})\) when \(M(\ell,j)\), otherwise \(W'_{\ell,j}=W_{\ell,j}\). The finite golden Agda owner provides source-written terms for selection soundness, unselected-cell invariance, conditional idempotence, a toy two-axis removal/retention square, and a constructive no-decoder counterexample. A separate non-golden owner bridge imports the repository's existing compression/realization owners and proves the analogous collision firewall. Neither identifies the actual Qwen patch.

For a real vector direction \(u\) and a matrix column \(w\), a mathematical target worth separately proving is \(P_u w=w-u(u^\top w)/(u^\top u)\), assuming \(u^\top u>0\). Then \(u^\top P_u w=0\) and \(P_u^2=P_u\) in exact arithmetic. **The published numerical patch is not automatically equal to this exact orthogonal projector.** Recovery of actual floating-point constants, scaling, basis, selected-index lists, and BF16 cast behavior is a separate same-object obligation.

### Precise BIDI/commuting squares

```text
external checkpoint hash + tensor names + selected indices
    | real tensor extractor                 | exact patch diff
    v                                       v
Agda layer/column/weight carrier -------> finite masked edit
    | semantic observer                     | semantic observer
    v                                       v
actual runtime on fixed decoder -------> held-out paired effects
```

Only the top abstract mask square has source-written proofs in this tranche. The real extractor, exact BF16 witness, runtime model execution and measured causal changes are **open**. An experimental score alone is not a weight-mechanism identity or a proof of preserved ability.

## LILA/E8 learner cross-PR reconciliation (2026-11-03)

The focused [WSP × LILA/E8 reuse ledger](WeightSpaceProgrammingLilaE8Reuse20261103.md) inspects actual unmerged #1094 (semantic intervention), #1095 (E8 quantizer, rank-one attention bias and shared Q/K orthogonal gauge), #1265 (Dust forward-only real-projection adapter with only local analogue runtime receipt), and #1442/LeechTransformer #4 (E8-first prior/history). The actual accessible Sovereign-LILA mirror sources `models/model.py` and `training/train.py` were inspected. A pure shared orthogonal Q/K coordinate transform preserves ideal dot-product scores and should not be cited as an intervention that fixes repetition. E8 geometry, root counts, rank-one score bias, and a Dust update are **distinct** from the edited 64+64 Qwen MLP columns.

The new golden candidate `DASHI.Reasoning.WeightSpaceProgrammingLilaE8InterventionExact` uses the existing standalone WSP finite owner and proves scope separation for projection, quantizer, attention, root-codebook and memory *state coordinates*. This is not an E8GPT runtime or output-noninterference theorem. A real source-root/hidden/parameter intertwiner and matched experimental controls remain open.

## Exact remaining max-cut (ordered)

1. **WSP-01, external custody:** Pin per-file Git revision and hash each external manifest, code, base model revision and edited artifact. Preserve the source-generated columns and names. Re-run `code/apply_edit.py` against exactly the pinned base checkpoint and compare both tensor SHA256 hashes. This also catches changed rounding and non-target writes.
2. **WSP-02, numerical fidelity:** Introduce Agda finite `Fin` indices for 24 layers, 1024 output rows, 3584 MLP input columns; represent the exact 64+64 selected column lists, prove bounds/no duplicates, mask cardinality and exactly 131,072 addressed entries. Represent *bitwise BF16* changes separately, with the reported 130,188 distinct changed values. Prove source-to-Agda mask and patch decoding commute.
3. **WSP-03, projector/numerical proof:** Model the actual source patch formula in rational/real arithmetic, handle nonzero denominator, compare source edit with generic rank-one projector and its quantized approximation. Keep approximate residual direction suppression distinct from exact annihilation.
4. **WSP-04, inference/same-object:** Establish Qwen3.5-specific tensor-to-operator bridge including normalization, MLP/SwiGLU, residual, Gated DeltaNet/attention, tokenization, generation settings and BF16 effects. Prove that the runtime loads precisely the edited checkpoint; no claim of runtime equivalence from abstract identity alone.
5. **WSP-05, causal and benchmark:** Pre-register exact fixed seeds/data/sampling; re-evaluate both source and modified model, paired negative/random/norm-matched controls and unedited/10/25/50 regimes. Report bootstrap uncertainty, memorization/contamination checks, output truncation, and net changes in accuracy/length. Separate causal localization, removal of loops, and new generalization.
6. **WSP-06, cross-system reuse:** For Qwenputer, Leech/MoE/federation, test patch-then-quantize vs quantize-then-patch, revision custody, content-addressed transport and selected expert history. A changed checkpoint or routing graph must invalidate stale inference caches until updated or revalidated.

## Executed bounded manifest audit (not kernel acceptance)

The connected-source JSON manifests were parsed and checked in this review: two tensors, shapes 1024×3584, 64 distinct bounded columns each, 131,072 addressed positions, 130,188 BF16 changed entries, 884 rounded-back positions. The new repository script `scripts/check_weight_space_programming_p50c_manifest.py` provides repeatable local checks (not yet independently executed in this session). Structural source checks confirmed the `--safe` header, absence of postulate/hole spellings and separate non-golden legacy bridge. These checks are **not** a proof of the tensor hashes, the actual floating-point edit or Agda typechecking.

## Verification/provenance limits

Source-written `--safe` Agda proof terms are not yet evidence of typecheck acceptance. No Agda executable or actual Qwen weights were available in this execution environment. No real checkpoint was downloaded, edited or benchmarked, and no CI was run. Do not call these results an MIT replication, independent discovery of weight-space programming, or a completed same-object proof.
