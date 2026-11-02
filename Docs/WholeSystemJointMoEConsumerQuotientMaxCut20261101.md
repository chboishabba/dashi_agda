# Whole-state quotient, not four router packets — max-cut correction

**2026-11-01.** Owners: LeechTransformer PR #4 and DASHI Agda PR #1442.

## 1. Correct global object and per-consumer quotient

The shared historical state is `Z_t=(x_t,H_0,...,H_{E-1},modelRev,historyRev)`.
It is **not** `E` independent `(x,H_e)` pairs. The model computes a
top-k route and weights using all histories **where that knowledge lives**.
When the source retains the router, the worker need only execute the k
selected experts and return their unweighted outputs; the source retains
the weights and aggregates them.

An admitted selected-only remote consumer receives the quotient
`Q_S(Z)=(x,(H_e)_{e∈S})`, plus route IDs and versioned execution authority.
All unselected histories remain at their authoritative owner. This is a
*consumer-specific* quotient, NOT a same-state identity for an arbitrary
consumer. It is correct only if the target worker executes exactly the
selected expert functions against the correct versions, and no downstream
consumer silently asks for inactive histories.

The Agda `LeechJointStateConsumerQuotientExact.agda` constructs the
shared-activation/selected-history projection, a dependent reopening,
pointwise selected and inactive history laws, a consumer fibre-constancy
criterion, and a conditional full-state replay when retained inactive
histories agree. It is a source-written `--safe` leaf; **Agda kernel not
run in this turn**. Reuses `Core/ConsumerQuotientBaseChangeExact`,
`Reasoning/HistoryTimeIndexedConsumerFibreExact`, and the finite
`LeechGenericHistoryActionTransportExact` owner as its proof context.

## 2. Source-implemented exact joint wire format

`scripts/federated_joint_state_quotient.py` defines JQ1, a bounded,
versioned, content-checked *selected-execution* packet with a single
activation and k selected histories, not k copies of x. Compares three
complete framed candidates:
- uncompressed shared-selected state;
- ordinary zlib over the **joint** state (cross-array redundancy visible);
- ordered predictor/orbit/correction stream.

Its predictor tournament reuses the shared x, exact IEEE sign(x), prior
reconstructed selected histories and their signs, and optionally a
receiver-owned **acknowledged** baseline. This is encoded as references
+ exact XOR residuals, jointly entropy-coded. If a component equals a
representative or signed/permuted representative, its residual has zero
bytes. Any difference gets its complete XOR correction; arbitrary floats
are never forced into a false orbit class. It can fall back to the
shortest full framed raw/zlib/orbit representation.

`scripts/punctured_nine_exact_site_actions.py` adds bitwise exact
centre-preserving punctured `F3²` site permutations (point inversion,
coordinate swap, order-three maps and shears), and their amplitude-sign
compositions as candidate predictors. This reuses the actual
`OggSSPP2BalancedTernaryPuncturedPlaneExact` eight-point enumeration;
`LeechPuncturedNineSiteActionsExact.agda` proves its finite order-3,
order-2, S3 conjugation and commuting point-antipode laws in source.
An ambient GL(2,F3) sheet permutation is **not a proved Leech lattice
automorphism or a semantic opposite argument**.

A temporal reference is permitted only with a caller-supplied acknowledged
revision, byte-matching receiver snapshot, and explicit model/history
versions. Packet hash is integrity/accidental mismatch detection, **not
authentication**. Surround JQ1 with `scripts/federated_authenticated_session.py`
HMAC envelope for session/sequence/source-revision admission.
That existing in-memory HMAC session is **not** AEAD confidentiality or a
crash-atomic durable exactly-once protocol.

## 3. Critical FULL network cost, not forward-only compression

For d=384, E=4, top2, FP32:
- E raw copied `(x,H_e)` pairs = 4×3072 = **12,288 B**, repeated x;
- one x + all four H = **7680 B**;
- all four projected router features = **9216 B**;
- selected execution input one x + two H = **4608 B**, *before JQ1 framing*;
- if source owns H, worker must return 2 unweighted expert outputs PLUS 2
  updated histories = **6144 B** before reply framing, so raw complete
  request+response is **10,752 B**;
- if worker retains H and acknowledges the new revision, it can return
  two unweighted outputs (**3072 B**) plus ACK/version/provenance;
- alternative remote aggregation transmits explicit source-certified
  mixture weights then returns one aggregated output, requiring a separate
  weight-transport receipt. JQ1's current default is **source aggregation**.

The 25% router-feature-width reduction is an INTERNAL model property.
Sending every projected router feature from a central source can exceed
sending one shared activation and histories. Even 4608 B of selected
inputs is not necessarily optimal: with shared ACKed history, a local
reusable operator and a consumer-sufficient quotient, source may send
only a signed/action witness plus residual correction.

Ideal serialization at 1Gb/s for 10,752 B bidirectional is 0.086016ms
(excluding metadata/headers); at 10Gb/s, 0.0086016ms. With an example
5ms RTT, isolated requests are RTT-bound. Large/batched state migrations
are byte-bound. These are link arithmetic, **not actual WAN measurements**.

## 4. Proof and implementation tests

- `HistoryOrbitMoE.execute_selected`: selected expert computations
  without recomputing the global router. If caller supplies weights it
  returns their aggregate; otherwise returns k **unweighted** outputs,
  allowing source-side mixing and avoiding weight transmission.
- `tests/test_joint_selected_moe_execution.py`: original whole
  `step` versus JQ1 unpack→selected execution→source mix→all-H rejoin
  for all opt-in geometries, plus full multi-token historical replay.
- `tests/test_federated_joint_state_quotient.py`: full-bit IEEE sign,
  high-entropy cross-expert orbit, raw fallback, ACKed temporal updates,
  source/revision/consumer failures, HMAC session tamper and replay.
- `tests/test_exact_punctured_site_orbit.py`: S3/C3/C2 permutations,
  sign-composed geometric residuals, exact IEEE payload and ablation.
- `scripts/capture_joint_moe_state.py`: strict trained-MoE loading,
  records real normalized activations, full E pre-step histories and
  admitted routes at each token; verifies captured recurrent final
  history against actual model forward. The old `best_model.pt` is
  DENSE and correctly rejected as a MoE geometry capture.
- `scripts/benchmark_joint_state_quotient.py`: NPZ actual-capture
  benchmark records complete framed bytes, measured local encode/decode
  costs, raw-vs-quotient winners at 1/10Gb/s, and BOTH source-owned
  histories (return k outputs+k histories) and peer-retained histories
  (return k outputs+explicit ACK assumption).
- All new regressions are **committed source, not yet executed in the
  full checkout**. Previously user-verified 66 passing tests and the
  exact SymPy Fourier certificate predate this work; do not reuse those
  numbers as verification of new JQ1 files.

## 5. How to run on the actual student (not a synthetic MoE)

```bash
git fetch origin experiment/consumer-preserving-multiscale-codec-20261031
git switch experiment/consumer-preserving-multiscale-codec-20261031

python -m unittest \
  tests.test_federated_joint_state_quotient \
  tests.test_exact_punctured_site_orbit \
  tests.test_joint_selected_moe_execution \
  tests.test_benchmark_joint_state_quotient \
  tests.test_capture_joint_state -v

# Once actual signed-wave MoE candidate weights and heldout token IDs exist:
python -m scripts.capture_joint_moe_state \
  --checkpoint artifacts/signed_wave_full_model.pt \
  --token-ids /path/to/heldout_token_ids.npy \
  --layer 0 --device cpu \
  --output artifacts/real_joint_layer0.npz

python -m scripts.benchmark_joint_state_quotient \
  --capture artifacts/real_joint_layer0.npz \
  --history-placement source \
  --output artifacts/joint_source_owned_receipt.json

# Counterfactual placement: peer-held histories need authenticated ACK
python -m scripts.benchmark_joint_state_quotient \
  --capture artifacts/real_joint_layer0.npz \
  --history-placement peer \
  --output artifacts/joint_peer_owned_receipt.json
```

Provide real receiver-baseline captures and authentic session ACK revisions
before running the `--ack-revision` comparison. No automatically fabricated
future history/semantic label is permitted.

## 6. Highest-value remaining real proof and measurement

The new codec proves bytes can reopen *if* the exact receiver snapshot
exists; it cannot prove an untrained model spontaneously possesses
compressible geometric correlations. Need actual trained students/real
corpus and capture to measure: fraction of history deltas with zero
correction under point sign, punctured-site S3/C3 actions, cross-expert
reuse, temporal ACK baselines, and matched model-quality/latency outcomes.
Where action transforms learned *computation*, also require the actual
router/weights/historical state commuting witness (or full correction),
not merely a geometric byte permutation.

Original Leech-LILA architecture by Anatolii Kornienko. DASHI original
geometry, j369, consumer-fibre, temporal codec and Sophontic/intervention
proof ownership follows existing source attribution. The phase nine
C3×C3 is NOT cyclic C9; no ESD edits or Monster 3B ownership reassignment.


## 7. Dataset/provenance cut resolved at source level (1 November)

The missing `.npy` arrays are generated artefacts, **not** missing
mathematical datasets. LeechTransformer has `vocab/e8_morpheme_.model`
(the saved original SentencePiece model),
`training/train.py` / `data_utils/streaming_dataset.py`
(FineWeb-Edu train skip first 5000, validation first 5000), and an
earlier `notebooks/lila_leechtransformer-new.py`
(`roneneldan/TinyStories`). Its published TinyStories corpus has
independent train/validation splits. All generated token ID arrays
must use the *actual* checkpoint tokenizer and retain disjoint source
documents, source revision, independent heldout split and data hashes.

LeechTransformer PR #4 now adds
`scripts/prepare_real_leech_tokens.py`,
`scripts/run_real_moe_jq1_experiment.py` and
`tests/test_prepare_real_leech_tokens.py`.
The one-command pipeline streams real corpus samples, fits both
`c2_invariant` and `punctured9_wave` history-MoE students from the
same frozen dense teacher, separately evaluates full-model heldout CE
and then records actual selected history reuse/codec Pareto.
This resolves the **inputs/experimental procedure** max-cut but NOT
the empirical quality/compression result: no local training process
was executed by the GitHub connector. TinyStories text is originally
AI-generated short stories: real corpus rather than random token IDs.

Formal promotion gate: provenance-compatible source → verified tokenizer
identity → disjoint training/heldout → trained non-synthetic student →
causal route/history replay → exact JQ1 reopening → consumer quality +
bidirectional bitrate and latency comparison. Do not substitute the
prior two-sequence synthetic smoke score or 82-pass earlier branch
verification for an actual learned-student result.


## 8. User-executed real-text gate: failure is learning, not codec admissibility

User ran the original checked-in vocabulary on 64 TinyStories training and
32 disjoint heldout sequences, one epoch, and completed the manual student
pipeline after an ITIR-venc interpreter-finalisation crash in the
orchestrator. Dense teacher heldout CE=2.58.
The `c2_invariant` 12-layer MoE achieved CE=8.63, and the
`punctured9_wave` MoE CE=17.30. Both are *worse* than the uniform
2048-class log-loss `ln 2048 ≈ 7.625`. These students are NOT usable
replacement learners. This does not falsify the geometry of the
punctured T² wave representation: the trained student is deeply
undertrained and every FFN was independently replaced.

Each geometry produced 2048 captured token frames with byte-exact JQ1
reopening, 9.25–9.26MB wire versus 10.07MB raw framed, and no winning
punctured-site, signed, previous-history or temporal orbit predictor:
every frame selected plain joint zlib. Under 1Gb/s assumed RTT and the
measured local encoding costs, ~11.42ms JQ1 vs ~5.16ms raw. Both
quality and transport Pareto gates FAIL.

**Previously missing mathematical separation now formalised** in
`DASHI/Reasoning/LeechPerExpertSymmetryDoesNotForceHistoryReuseExact.agda`:
even two experts with *the same* perfectly C2-equivariant identity
history transition can retain histories in disjoint C2 orbits
(one centre, the other noncentral). A per-expert conjugation proof cannot
force within-sample cross-expert exact compression. No reclassification
of semantic dissent as a negated activation is warranted.

The high-alpha source-level diagnostic is now
`LeechTransformer/scripts/diagnose_moe_quality_collapse.py` with
regression `tests/test_moe_quality_collapse_diagnostics.py`. It isolates
single-layer teacher→student substitutions, cumulative prefix
replacement, same-teacher-input FFN relative MSE, router entropy,
expert load, signed orientations and recurrent history amplification.
This distinguishes cumulative distillation error, one catastrophic
layer, and route-scale collapse *before* another large training run.

Run the diagnostic on the user's saved real student checkpoints and
original heldout split; the GitHub connector cannot access their local
`/tmp/real_text_moe_jq1_smoke` directory or execute the new scripts.
Agda kernel status: new no-go source written with `--safe`, **not
kernel checked**.


## 9. E8-first correction and quality-guarded shared canonical-history programme

The model's 384D width admits 48 coordinate charts of rank 8, grouped
three per 24D block and six per 48D attention head. **E8** is the
natural candidate rank-eight root-lattice inductive prior (240 actual
roots), not the *eight points* of the punctured 9 index carrier.
DASHI's earlier E8/Leech sources and engineering-only
`LilaE8InitialisationPriorNote.agda` are explicitly reused in
`Reasoning/LeechE8PriorStrataBidiExact.agda`.
The neural model's currently trained QR Q/K gauge and E8-named
tokenizer do not themselves certify the prior.

Companion Python PR #4 now has executable `e8_root_invariant`
routing with all 240 E8 roots, mathematically valid root reflections
and numerical Weyl invariance tests, distinct from punctured-nine.
It adds opt-in `moe_guarded_ffn` with teacher FFN residual at
gate zero and progressive calibration on a split drawn only from
training data. The untouched HELDOUT evaluates real quality after
each experiment. Failure of standalone candidate CE=8.63/17.30
cannot be papered over by a zero-gate fallback: the full teacher
remains in memory and no parameter saving is claimed.

New `Reasoning/LeechSharedCanonicalOrbitHistoryExact.agda` proves
the arbitrary-E re-opening law for one canonical history and E
invertible action charts. It supplies the missing *structural
assumption* for compressibility that the old per-expert C2 proof
does not entail. The Python `E8SharedOrbitHistoryMoE` maintains
that invariant by construction, updates the single canonical
source from route-weighted selected proposal inversions, and
reconstructs arbitrary selected memories after dispatch.

New JQ1 `shared_e8` can transmit one canonical history even when
none of the selected expert IDs is the identity-chart owner, plus
independently approved E8 action witnesses and every necessary exact
byte correction. It is not a magical lossless compressor for
arbitrary independently trained expert histories. Same learned
model must pass task-quality and historical replay gates before any
network improvement is promoted.

User's prior 64/32 TinyStories 1-epoch result and 82 passing tests
are historical evidence; new E8/guarded/shared-orbit source code is
not kernel-checked or full-suite-executed in the current connector.
For local commands and exact remaining max-cut, use the companion
`LeechTransformer/docs/e8_first_quality_guarded_joint_history_maxcut_20261101.md`.

Distinct ownership: E8 root system and Weyl group are classical
mathematics, source formalized in prior DASHI Agda; Leech original
engineering architecture by Anatolii Kornienko; finite F3²/
punctured-nine, modular j and Sophontic argument opposition are
independent operators with independent proof contracts. No Monster
or ESD owner is overwritten.

## 2 November max-cut: revalidated gates and strict teacher erasure (source-written)

**Problem boundary.** A teacher-retaining hybrid at gate 0 matches the
original dense inference, but it has not replaced a dense FFN. A partially
opened gate also retains all dense weights. Reusing gate decisions after
an optimizer update is unsafe without rechecking the changed student.

**Implementation receipts (LeechTransformer PR #4):**

- `scripts/train_guarded_moe_continuation.py` now revokes every former
  gate before recalibrating each optimizer revision. Its zero-gate
  dense fallback is explicitly rechecked on train-only calibration data.
  Exact training/heldout token-window overlap is rejected for direct
  callers that bypass the dataset preparer.
- `scripts/promote_guarded_moe.py` refuses any gate not **exactly 1**.
  It strips all original `.ffn.` and `.quality_gate` parameters,
  strictly reloads the independent teacher-free model, and compares
  its logits against the full-gate hybrid. It evaluates full-model CE
  independently against the pinned original dense checkpoint. The
  CLI requires the guarded source SHA and the prior independent
  heldout-pass receipt. It refuses to write a promoted checkpoint
  when these conditions fail.
- `scripts/run_real_moe_jq1_experiment.py` invokes that export only
  when the full-replacement gate passes. Otherwise its consolidated
  report explicitly records why no standalone model exists.
  Capture and JQ1 continue to diagnose candidate histories
  without implying a quality or network win.
- `E8SharedOrbitHistoryMoE.reconcile_selected` additionally refuses
  negative/non-normalised/nonfinite routing weights and nonfinite
  selected updates before the authoritative shared history is merged.
  This is local data validation, NOT authenticated distributed commit.
- Source-written regression suites:
  `tests/test_guarded_moe_continuation.py`,
  `tests/test_teacher_free_promotion.py`,
  `tests/test_e8_canonical_history_jq1.py`.
  They have **not** been executed via this GitHub-only editing session.

**Agda contract (DASHI PR #1442):**
`Reasoning/LeechQualityGateTeacherErasureExact.agda` gives a
`--safe`, source-written finite-layer **conditional** theorem:
the hybrid and teacher-free traces are equal for every finite
execution schedule *if every gate has a proof of full admission*.
Gate-zero teacher identity is a separate lemma. Numeric intermediate
gate values, PyTorch floating-point parity, source authentication,
training CE and real E8 action adequacy are NOT derived. The module
has **not been Agda kernel-checked**.

**Exact remaining gates:**

1. **M0 (formal):** Agda kernel-accept the new gate/trace lemma and
   existing canonical-history proof with the pinned DASHI toolchain.
   Import them into the intended golden ownership graph if accepted.
2. **M1 (diagnostic):** Execute both existing failed-student
   isolated-layer/prefix CE and history-norm diagnostics on the saved
   original real-text split, without fabricating student data.
3. **M2 (quality):** Refit and recalibrate under a disjoint training
   calibration partition. Obtain positive nonzero gates. Then satisfy
   the **all-gates-one**, final heldout CE and strict standalone
   export contract. Zero-gate teacher parity is NOT sufficient.
4. **M3 (geometric reuse):** Run the independent E8-route and actual
   shared-canonical-history ablations with matched split, seed,
   capacity and updates. Inspect exact orbit corrections from real
   captured states rather than theoretical constructed actions.
5. **M4 (network):** Compare full request + response + ACK + versioned
   state ownership and measured encoder/decoder time. Choose raw on
   links where compression overhead dominates; no real WAN claim.
6. **M5 (semantics):** Only paired, independently scored intervention
   and trialectic-face tasks can establish reasoning quality, not
   signed-orbit matching or language cross-entropy alone.

**Source/attribution boundaries.** Original Leech-LILA author
Anatolii Kornienko (DOI 10.5281/zenodo.18784424).
Existing E8/Leech origins and Ibrahim Monster 3B work retain their
separate authorship. This DASHI theorem and the LeechTransformer
source implementation are repository-authored reconstructions, not
results attributed to those external authors. E8 coordinate actions
are not Leech lattice automorphisms without a separate proof.
No ESD modules were edited. **Previous measured quality gate still
fails**: dense CE 2.58; C2 CE 8.63; punctured-nine CE 17.30 on the
reported 64/32 TinyStories sample. No new quality numbers are claimed.

### Additional 2 November transport Pareto cut: policy before encoding

`scripts/benchmark_joint_state_quotient.py` now uses the first
half of captured frames to select **raw or JQ1** for each 1/10 Gbit/s
assumed link. It then reports the unchanged policy's whole-message
cost on the subsequent half. The full estimated round trip includes
measured local encode/decode CPU time, both serialisations and the
stated RTT/ACK/response-size assumptions. Small packets no longer
count as a gain if the predicted total latency is worse. Fewer than
four captured frames default to raw (insufficient calibration).
`tests/test_joint_transport_latency_policy.py` gives deterministic
slow-encoder and heldout-distribution-shift counterexamples.
This is a **prior-profile decision simulation**, not a real remote
deployment, authenticated state-owner protocol or measured WAN.
The actual request API already supports `permit_compression=False`;
deployment must select that before encoding, from a revision-bound
profile, rather than running both encoders on every message.
New tests are source-written and have not been executed here.

Focused local checks (optional; no CI dependency):
```bash
python -m unittest \\
  tests.test_guarded_moe_continuation \\
  tests.test_teacher_free_promotion \\
  tests.test_e8_canonical_history_jq1 \\
  tests.test_joint_transport_latency_policy -v
```
