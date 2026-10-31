# DASHI × Leech-LILA × Sophontic: a symmetry-bearing learner and federated computation
**Date:** 2026-10-31. **Owners:** LeechTransformer PR #4; DASHI Agda PR #1442. This is a synthesized formal *research and implementation* architecture, not a public claim of winning model-quality benchmarks.

## 0. Original object, not a standalone codec

We are studying a SMALL learned reasoning system with geometric memory, not a giant network whose activations merely need zlib. The measured checkpoint was a **dense** 12-layer, d=384, 8-head, vocab=2048, block=512 model. The actual source says its QKV is learned and multiplies Q and K by the same QR-generated orthogonal 24×24 matrix; mathematically their inner product is unchanged. This is *not* a demonstrated Leech-lattice automorphism. The measured checkpoint has lambda_geo=0; the optional resonator is not attached by default. The official Leech-LILA paper/README reports other geometry-training experiments; attribute them to original architect **Anatolii Kornienko**, do not silently assign those claims to this checkpoint.

The real architectural decomposition is:
- `384=16×24=128×3`: sixteen 24D chart blocks and 128 three-coordinate trialectic sites per layer.
- `48=2×24=16×3`: each of eight heads spans two 24D blocks / sixteen triads.
- These are coordinate and computational resolutions, **not** an identification of 24 Leech directions with 27 ternary states.
- DASHI's local `T³` ternary triad has 27 states and one fixed centre + 13 antipodal pairs / 14 orbit classes; `T⁹=(T³)³` has 19,683 states; the structured three-cell boundary can retain six independent triad cells plus a nonfactorable triadic face. These state counts are *not* 27 trainable experts or 19,683 weights.

## 1. Four distinct symmetry/evidence coordinates

**C2 / sign:** simultaneous antipodal action on activation, expert history, and outgoing orientation. This is NOT argument disagreement, logical negation, ethical valence, or automatically a Leech automorphism.

**C3 / trialectic phase:** cyclically rotate each real triple (a,b,c)->(b,c,a). The orthogonal 3-point real Fourier rechart is:
  DC=(a+b+c)/sqrt(3);
  Re=(2a-b-c)/sqrt(6);
  Im=(b-c)/sqrt(2).
C3 rotates (Re,Im) by 120 degrees; C2 globally negates all three. They commute as actions on the coordinate triple, but are *different* group elements. Their learned representations and physical interpretations require tests. In code, `models/trialectic_wave_prior.py` realizes the 384D rechart, inverse, C3 generator and invariant routing features. It is a real finite DFT, not a quantum algorithm.

**Irreducible face:** `TrialecticBoundaryFaceNonfactorabilityExact.agda` exhibits the SAME three dyadic edges with different triadic face relations. Hence `three dyads -> face` is not a universally valid inference. The full learner must be able to retain an independent relational/face state, new evidence, or an explicit corrective residual. `DenseToSignedExperts.face` is a separate optional context pathway with zero output at initialization; without supplied face evidence it is NOT trained or semantically licensed.

**Semantic paired intervention:** Sophontic's publicly described evaluator uses paired load-bearing perturbations and flip rate; its site claims a compact geometric model beats some larger models, but the unreleased model and claims are not independently validated here. DASHI already owns non-antipode argument response types, nonfactorable trialectic faces, 369 ultrametric observers, wave phase and prior Sophontic paired semantic/action bridges (Agda PR #1094/#1095/#1265). These are reused as the basis for *training the right type of response*, rather than inferring response labels from `sign(x)`.

## 2. Signed expert mod is a learnable quotient, not a moral binary

For joint state z=(x,H_e), define a trained signed chart s(z) with s(-z)=-s(z) for non-fixed states, with an explicit fixed-centre rule. Let `F_e` be a nonlinear expert and `U_e` its history transition. Define
  `O_e(z)=s(z) F_e(s(z) z)`,
  `H'_e(z)=s(z) U_e(s(z) z)`.
Then `O_e(-z)=-O_e(z)` and `H'_e(-z)=-H'_e(z)` in exact arithmetic, WITHOUT demanding the underlying `F_e` or `U_e` is odd. The same trainable expert family handles both oriented charts, reducing duplicated parameters. The previous raw router failed this law: `topk(r(x,H))` may change after sign inversion.

New opt-in `route_geometry=c2_invariant`: the router consumes `abs(x),abs(H)`; hence routing IDs and softmax weights are invariant to joint C2 inversion (subject to floating-point implementation). This is a **model inductive bias**, not a wire codec. Learned orientation receives an odd bias-free linear score; exact zero-score nonzero states use first-nonzero-coordinate sign as the antipodal tie-break; zero state maps to fixed centre.

New opt-in `route_geometry=c2c3_wave`: the router consumes per-triad |DC|, rotating-plane power and |abc|. The features are C2 and C3 invariant within floating tolerance. The actual expert outputs are C2-antivariant by construction, but **not automatically C3-equivariant** because their nonlinear networks are not constrained by the C3 action. A C3 output law requires another verified action/intertwiner or an exact correction.

Full MoE equation: `M(x,H)=sum_{e in TopK(r(x,H))} w_e(x,H) O_e(x,H_e)`. Under transformed action g, the selected expert-index permutation, weight law, expert outputs AND history update must each commute. Imported DASHI finite owners: `LeechGenericTopKActionTransportExact`, `LeechSignedWeightedMixtureActionExact`, `LeechGenericHistoryActionTransportExact`, `LeechFullOutputHistoryTraceBidiExact`. No conditional theorem is a proof that the actual learned router has the law unless the implementation is checked.

## 3. Exact dense checkpoint transfer: retain invariant AND oriented components

An entirely odd FFN would discard the even computation. GELU itself satisfies `GELU(x)-GELU(-x)=x`, with linear odd part x/2 and nonlinear even part. More generally ANY deterministic dense FFN `F` has:
  `E_F(x)=(F(x)+F(-x))/2`,
  `O_F(x)=(F(x)-F(-x))/2`,
  `F(x)=E_F(x)+O_F(x)`.
No activation symmetry or task assumption is needed for the exact parity decomposition.

`DenseToSignedExperts` uses the actual frozen trained dense FFN as teacher:
  * `even_student(canonical_even_input(x))` learns E_F; unlike `abs(x)`, global sign canonicalisation retains relative signs.
  * history-bearing `HistoryOrbitMoE` learns O_F via a C2 invariant route and sign-conjugate experts.
  * optional face MLP consumes EXPLICIT independent face context, not automatically inferred from dyadic edges.
  * `blend=0` reproduces the original dense forward, and `predict_only` removes the teacher from student computation.
  * an exact **correction** `R(x)=F(x)-[E_student(x)+O_student(x)+Face(x)]` is measured. Zero *measured* residual on a finite set is not a theorem for all inputs; to transport without correction one needs actual consumer-level equivalence or an exact reconstructive witness.

`scripts/train_signed_wave_experts.py` trains both students against the original dense FFN with heldout examples and saves all layer adapters. `scripts/export_signed_wave_model.py` converts ONLY when adapters for all layers exist, preserves all other trained transformer weights, creates a strict-load student model, and computes heldout full-model logits and next-token CE relative to dense. This is the first practical path from 12-layer teacher to full 12-layer geometry-bearing student. Learned semantic/geometric benefits must then be judged by **paired reasoning quality, generalisation, and cost**, not by a sign symmetry alone.

## 4. Parameter and execution Pareto at d384

A dense 384->1536->384 FFN has 1,181,568 parameters per layer (with biases). Example student configuration E=4, k=2, expert_width=192, 24-rank history factorisation:
- sparse signed expert family + routers + history: approximately 1,037,574 parameters / layer;
- independent even student: 148,032 / layer;
- total deployable even+odd: **1,185,606 / layer**, nearly the same full parameter count as the dense FFN, though two of four experts are active per token;
- optional face pathway: 295,680 parameters / layer, not included until face evidence/training exists.
- full history transition weights alone: 21,233,664 across 12 layers and four experts. Rank-24 factored transition weights: 1,769,472 (12× fewer weights in this part). This includes only matrix weights, not biases.

A smaller number of *active* expert weights does not imply lower latency without hardware/memory profiling. Compare shared dense FFN, raw-sign MoE, C2-invariant routing, C2+C3-wave routing, rank24/no rank, even+odd/odd-only, with and without trained face context. Compare training token count and optimizer, heldout loss, paired flip-rate **and paired correctness**, action composition and nuisance robustness. Also record phase locking, action residual, operator reuse, effective rank, condition number, and grokking transition times against earlier DASHI/LILA metrics. A sign should not be interpreted as moral polarity.

## 5. Federated and cryptographic consumers are downstream of learned structure

A peer should be offered five alternatives (local inference, remote dense activation, remote exact compressed activation, acknowledged history delta, admitted geometric/operator action), all evaluated by total time:
  `T = local_compute + encode + wire_bits/bps + RTT_count*RTT + remote_compute + decode + ACK/replay + queue`.
At 1 Gbit/s, 1 MiB serialization is 8.389 ms; at 10 Gbit/s it is .839 ms. The REAL dense checkpoint receipt passed full/KV-cache parity (max logit difference 9.5367e-6); exact activation decode produced 23,004 B adaptive vs 24,784 B raw (1.077×); actual codec overhead made raw win on both 1/10Gb links in that one-run 5ms-RTT bidirectional model. This is not a bound on temporal, operator, dictionary or consumer-relative geometry compression.

A sign chart and learned phase may allow a peer to send a reusable representative + action + complete corrective residual instead of a tensor, **only** when a consumer-relative commuting square admits it. A history reference requires authenticated version, session/nonce, ACK and receiver-side durable state. Local HMAC checks are not encrypted transport, privacy guarantees, or exactly-once remote inference. Costing must include expert model/state migration and possible duplicated cache/optimizer memory. Do not collapse transport receipts into semantic/truth authority.

## 6. Exact tests and provenance

Already in DASHI:
- `TrialecticBoundaryFaceNonfactorabilityExact.agda`: boundary collision/no face descent.
- `Trialectic369HypervoxelUltrametricExact.agda`: observer matrix ↔ T9 and exact prefix ultrametric.
- `TrialecticThreeCellHyperformSynthesisExact.agda`: T3 participant cells, independent face and structured six-cell boundary.
- `BalancedTernaryAntipodal369OrbitHierarchyExact.agda`: T1/T2/T3 fixed centre, 1/4/13 antipodal pairs, quotient counts 2/5/14.
- `TernaryHypervoxelPermutationTransportExact.agda`: S3 exact coordinate transport, push/pop/joins.
- `Physics/WaveAlgorithmLift.agda`, `Moonshine/JInvariantColourWheelWaveSignedBidiExact.agda`: finite phase/wave, not literal physical quantum state.
- `Core/ArgumentResponseNonGeometricOppositeBidiExact.agda`, Sophontic PR #1094/#1095/#1265: structured semantic opposition, intervention fitting, paired outcome controls.
- `Core/ConsumerQuotientBaseChangeExact.agda` and `Reasoning/HistoryTimeIndexedConsumerFibreExact.agda`: observer-relative quotient and historical gluing.
- `DASHI/Reasoning/LeechParityC3ActionKernelExact.agda`, `LeechSignedWeightedMixtureActionExact.agda`, `Leech369TrialecticWaveLearningArchitectureBidiExact.agda`: new signed/C3/384D bridge laws. Agda kernel **not run here**.

Local CPU analogue checks of the opt-in C2/C3 wave signed MoE:
  * d48, E4, k=1/2/4: route+weight equality under inversion, output+history sign residual zero in sampled cases;
  * d384 wave3 inverse and C3 phase: maximum finite precision deviations ~3.58e-7; C3 invariant router features ~1.43e-6;
  * even/odd canonical decomposition and full autoregressive recurrence; parity output zero residual on sampled cases;
  * toy dense student gradient executable, loss fell from ~0.14437 to ~0.07819 over 11 updates on fixed random input.
These are **local source-equivalent CPU experiments**, not full checkout tests, user checkpoint retraining, semantic evaluation or formal verification. Existing user run 11/11 targeted tests refers to the earlier dense verifier branch, not these new commits.

External source / authorship boundaries:
- Anatolii Kornienko, Leech-LILA, DOI 10.5281/zenodo.18784424, original architecture claims separate from local branch implementation.
- Sophontic Inc. (https://sophontic.ai/), paired perturbation and geometric-density research marketing; original model-quality claims remain theirs, not independently established.
- DASHI synthesized 369, trialectic/wave, typed objection, historical fibre, compression and mathematical proof owners remain individually attributed in their source files, with original precedents including Serre (1977) and Dixon–Mortimer/Nekrashevych for finite group/carrier context.
- Pollux (https://github.com/alavicka/pollux), independent native Leech vector-ternary quantization research; compare codebooks only after respecting its own source and deployment/evidence bounds.
- No edits to ESD surfaces; do not reassign prior Ibrahim Monster 3B ownership or promote carrier fingerprints to Monster or Leech same-object theorems.

## 7. Run on real checkpoint

```bash
git fetch origin experiment/consumer-preserving-multiscale-codec-20261031
git switch experiment/consumer-preserving-multiscale-codec-20261031
python -m pip install torch numpy

# Use the REAL token IDs of the corpus that trained best_model.pt:
python -m scripts.train_signed_wave_experts \
  --checkpoint data/best_model.pt --config leech_dense_config.json \
  --token-ids /path/to/train_ids.npy --layer -1 \
  --experts 4 --top-k 2 --expert-width 192 \
  --transition-rank 24 --route-geometry c2c3_wave \
  --epochs 3 --device cpu --output artifacts/signed_wave_adapters.pt

# Evaluate with genuinely held-out token IDs:
python -m scripts.export_signed_wave_model \
  --checkpoint data/best_model.pt --config leech_dense_config.json \
  --adapters artifacts/signed_wave_adapters.pt \
  --heldout-token-ids /path/to/heldout_ids.npy \
  --device cpu --output artifacts/signed_wave_full_model.pt
```

All new submodules are opt-in. Existing dense checkpoint remains strict-load compatible. Do not interpret an exported candidate as a successful model until heldout language and paired semantic results support it.


## 8. Paired training and outcome test, separately from sign-chart training

New `models/paired_intervention_geometry_loss.py`: the supplied correct target for each member of a semantic pair is required. `paired_training_objective` uses both cross-entropies, plus an optional geometry penalty **only when a separate explicit action label** `identity`, `C2_inversion` or `C3_cyclic` was independently licensed for that sample. `none` is the default: a `challengeEvidence`, `alternativeExplanation` or `acceptWithQualification` kind never automatically assigns a negative sign, a flip or a specific latent action. It is differentiable and suitable for a later real end-to-end learning run. Gradient tests are source written, not claimed as a completed semantic training benchmark.

`scripts/eval_paired_semantic_geometry.py` loads the actual dense or exported student checkpoint and an NPZ with `tokens_a`, `tokens_b`, `targets_a`, `targets_b`, and `kinds` (one of the nine exact response categories in `ArgumentResponseNonGeometricOppositeBidiExact`). The evaluator reports **both members correct**, actual target-change frequency, predicted flip frequency, flip-decision accuracy, and independent identity/C2/C3 hidden-state fit without promoting it to semantic identity. A synthetic counterexample regression shows two different response kinds can map to the same antipodal geometry, and perfect flip rate can coexist with zero paired correctness.

```bash
python -m scripts.eval_paired_semantic_geometry \
  --checkpoint data/best_model.pt --config leech_dense_config.json \
  --pairs /path/to/typed_pairs.npz --device cpu \
  --output artifacts/dense_paired_receipt.json

python -m scripts.eval_paired_semantic_geometry \
  --checkpoint artifacts/signed_wave_full_model.pt \
  --pairs /path/to/typed_pairs.npz --device cpu \
  --output artifacts/student_paired_receipt.json
```

Interpret all outputs as **test evidence**. Neither an exact C2 equivariance law nor a high observed flip rate proves that a network reasons well, is safe, or is superior to Sophontic. The 384D/24D prior is a useful hypothesis to train, route and ablate, not an automatic semantic theorem.

## 9. Full-stream correctness

The same branch fixes the previous Q/K cache-mask offset bug for resumed chunks longer than one token: query mask rows must be indexed by `past_len:past_len+T`, not always `0:T`. `test_leech_moe_integration.py` now tests full vs cache equivalence under (2,3,2)-token chunks for dense, raw MoE and the deployed C2/C3 even+odd model. This is required for distributed replays in which a peer accepts multiple tokens between acknowledgments.

**Execution status:** the source-equivalent local PyTorch CPU check of the core signed-wave student, 3-point Fourier and odd/even distillation passed; a full checkout test suite, kernel checks and your actual 12-layer student training were not run here. The new paired dataset must be sourced with its own correct answers; absent source labels are not guessed.

## 10. The precise DASHI ordered 3+6=9 directional/chiral prior

Canonical finite owner is `DASHI/Foundations/TernaryGolay/ChannelC3OrbitDecomposition.agda`, **not** a fresh MoE hypothesis: nine ordered channels = three diagonals + six directed off-diagonal channels. The rotation group C3 partitions the directed channels into the *cyclic* (A→B→C→A) and *anti-cyclic* (A→C→B→A) triples. Transposing source/target exchanges these two orbits, while S3 sees one full six-channel orbit. The exact same channel decomposition is narrated in `Docs/support/reference/TernaryGolayCrossPollination.md`.

New `directed_trialectic_invariants(left,right)` in `models/trialectic_wave_prior.py` computes three C2/C3-invariant **bilinear** channels for each ordered real triple:
- self = aA + bB + cC
- cyclic = aB + bC + cA
- anti-cyclic = aC + bA + cB.

Swapping left and right swaps the cyclic and anti-cyclic channels, **not** the sign of the state. Under simultaneous inversion of both role vectors, all three channels are unchanged. This is a principled additional inductive bias that lets the signed expert router read *directional relational structure* instead of equating disagreement with a negative activation. The new `c2c3_wave` router consumes 3-point unary wave invariants of activation and these three signed relational channel sums against each expert's history. **The output expert is C2-conjugate, NOT proven C3-equivariant**. Ordered role assignment is essential.

The Agda bridge `Leech369TrialecticWaveLearningArchitectureBidiExact.agda` now reuses the actual channel owner's `channelCountIsNine`, `faceCountIsSix`, `diagonalCountIsThree`, C3 orbit-invariance, and chirality transposition law. Separately, `TrialecticBoundaryFaceNonfactorabilityExact.agda` proves these three dyadic edge values cannot infer every irreducible triadic face. Therefore a semantic/Sophontic response cannot be recovered solely from the three channel sums; an independent face history/context or explicit residual remains necessary.

Additional crucial Leech geometry caution: `Foundations/UBP/LeechValidMoveSet.agda` demands lattice membership/closure proof for a true Leech move; a sign flip on arbitrary ambient coordinates or C3 rotation of consecutive neural trits is NOT by itself a Leech group action. `Foundations/TernaryGolay/CoxeterToddRoutesBoundary.agda` describes an order-three Leech automorphism fixed-lattice route to K12 with separate unsatisfied same-object recognition; it cannot be silently used to certify this neural wave-coordinate action. `Docs/support/reference/TernaryGolayCrossPollination.md` credits independently authored ternary Golay code results (Noam D. Elkies et al.), and UBP work to Euan R. A. Craig. Those are mathematical donors, not source claims for this branch's trained expert model.

**Testing and evaluation:** local source-equivalent finite CPU check sees role swap exchange chiral channels and C2-invariant router with signed outputs/history for sampled states. The newly committed official branch Python tests and Agda module have not yet been fully executed/typechecked in this environment; full trained-checkpoint signed-distillation and heldout Sophontic paired improvement still require running on the local data.

## 11. Exact T9 tiling seam and scale-compatible fabric

384=16×24=128×3, **but** 384=42×9+6: a flat nine-coordinate observer matrix does **not** tile the width. Similarly 24=2×9+6 and 48=5×9+3. The first exact common complete tile is **three 24D blocks = 72 coordinates = eight nine-coordinate observer charts**. A model using T9 canonical observers must therefore retain residual/boundary/overlap data, use a legitimate cross-block grouping, or choose a different local consumer; it may not assume every 24D Leech block is itself one T9 hyperfabric. `Leech369TrialecticWaveLearningArchitectureBidiExact.agda` now contains exact arithmetic receipts and `geometry_shape` reports the 42/6 seam. This is a constructive architecture constraint, not a missing representation convention.

The feasible local learned routing prior is still eight triads per 24D block, using exact C3 Fourier and ordered 3+6 directed channels, with external face evidence. Larger T9 observers can be composed across blocks only when provenance, neighbour selection and consumer-relevant history are retained.
