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


## 2 November further max-cut — zero-gate student trace and same-model source provenance

**Golden Agda owner:** `DASHI.Reasoning.LeechQualityGateTeacherErasureExact`
now also contains:
- `studentRollout`: the teacher-free student trace evaluated
  regardless of the deployed layer gates;
- `studentRolloutIndependentOfGates`: for any two finite layer
  programs with **pointwise identical studentStep** functions,
  the student-only trace is equal for any finite schedule and initial
  state, even if their dense teacher implementations and gate values
  are different;
- `studentRolloutSameProgramEveryGate`: definition-level equality
  of one student-only trace and its underlying teacher-free trace.

`DASHI.Unified.LeechQualityGuardTOEBridgeExact` exports the theorem as
`toeStudentRolloutGateIndependent`, already imported by the canonical
`DASHI.Unifier` and `EverythingTOESymmetryResolved369` roots.
This is a **source-written `--safe` finite trace theorem**,
NOT an Agda-kernel-executed certificate this turn and NOT a proof of
end-to-end PyTorch differentiability or a bound on real trained CE.
Its precondition is exact equality of the student functions,
not an inference from the E8 root geometry or the numerology 3/6/9.

**Executable LeechTransformer PR #4 ownership:** the guarded
model implements `student_only=True` as a second independent
full network rollout. This branch bypasses the dense teacher
FFN and provides CE and teacher-KL training gradients even when
the deployed quality gate is zero. Actual quality requires measured
positive gates and eventually all gates one. The strict standalone
teacher-erasure procedure still checks weights, logits and CE; no
equivalence from a merely nonzero gate is allowed.

The same original model/file SHA-256 and source token-file SHA-256
are now bound to real JQ1 capture/benchmark receipts; a mismatched
pair is rejected before policy or arithmetic. Previously calibrated
model/history-revision-specific policy may choose raw/JQ1 before
encoding and wraps the selected-only JQ1 packet with existing HMAC
session authentication. No source-side selected top-k policy replaces
the authoritative consumer/state owner. The prototype's `verify`
does not call `commit`; durable execution and cross-peer ACK remain
open. This proof imports the existing
`LeechJointStateConsumerQuotientExact` and
`LeechSharedCanonicalOrbitHistoryExact` ownership boundaries
rather than identifying all histories with arbitrary true E8 orbits.

**Semantic M5:** the existing independently supplied labelled pair
evaluator remains separate from a newly implemented 2×2×2 trialectic
cube evaluator. The latter explicitly uses the 8 corner conditions
000,001,010,011,100,101,110,111 and requires the same fixed probe
token for all eight log-probabilities in a single third-order
difference. The independent gold targets at each corner determine
task correctness; a nonzero third-order difference by itself does
not prove semantic opposition, intervention independence, a
nonfactorable Sophontic argument, or lattice equivariance. Actual
source-labelled cubes and paired results are **not yet available or
executed in this edit**.

**Exact remaining proof/experimental frontier:**

1. Agda kernel-check `fullAdmissionPreservesEntireTrace`,
   `studentRolloutIndependentOfGates`,
   `everyExpertReopensSharedCanonical` and relevant TOE imports.
2. Audit faithful Python↔Agda concrete state/step correspondence;
   finite abstract trace equality is not same-object neural machine
   verification.
3. Run original real checkpoint and already saved failed students
   through train-only depth/route/history diagnostics.
4. Train a full student-only E8/shared-history candidate until
   strict teacher-free final heldout-quality export succeeds on
   unseen data; no result can be manufactured from a zero gate.
5. Run selected-expert byte-exact and task-quality ablations on
   the SAME promoted checkpoint and source split, then measure real
   roundtrip network including auth+ACK+remote computation.
6. Source labelled paired and 8-corner trialectic correctness
   studies; distinguish additive/multiway output interactions
   from external semantic and causal validity.

Attribution: Anatolii Kornienko owns the original Leech-LILA model,
DOI 10.5281/zenodo.18784424. Prior mathematical and repository
owners of E8 roots, Leech gluing, C3/369, finite consumers and
Ibrahim's Monster 3B remain credited in their original sources.
No *digital_esd*/ESD modules were edited. No tests, CI or
Agda kernel invocation are claimed for this tranche.


## 2 November — C2 train-only diagnosis and exact F-ledger synchronization

The source-written finite JQ1/teacher-erasure results are now accompanied
by a **user-executed diagnostic** for the original trained C2 candidate:
dense CE 2.54566636 versus student 8.60841485 over 4032 targets
(training split); layer-1 isolated substitution +3.42024 CE,
layers 0–1 +4.00670 CE. Teacher-forced layer-1 relative FFN MSE
86.6193 and RMS ratio 9.273. All logits finite. Route/sign statistics
come from only the first two sampled training sequences, not from
the entire split. User verified LeechTransformer PR #4 125 passing
tests plus 7 subtests, including a corrected zero-residual shared-E8
history decode. **The same numerical failures remain open; no
teacher-free student or WAN superiority has been demonstrated.**

The primary executable ledger is the new 2 November section of
`LeechTransformer/docs/e8_first_quality_guarded_joint_history_maxcut_20261101.md`.
Golden theorem owners/reuse and exact outstanding hypotheses:

- **F01 parity**: reuse
  `DASHI.Physics.YangMills.PhysicalInvolutionParityExact` and
  `LeechSignedHistoryExpertBidiExact`. Formally construct even/odd
  decomposition with declared additive/half laws. The scalar GELU
  reflection identity is a separate analytic authority boundary.
- **F02 odd-only error floor (OPEN)**: for an involution I and
  inner-product V, prove pair-MSE lower bound by norm² of target
  even component. This explains why a pure signed/odd network
  cannot model a non-odd biased dense teacher; it does not prove
  adequacy of the implemented even channel.
- **F03–F04 chart/action**: keep
  `conjugateIntertwinesInverse` separate from a concrete router,
  selected top-k weights/tie-breaking and full recurrent-state
  equivariance. Reuse `LeechGenericTopKActionTransportExact`.
- **F05–F06 learning gate**: reuse
  `studentRolloutIndependentOfGates` and
  `fullAdmissionPreservesEntireTrace`, including full gates
  as an explicit premise. Actual numerical autograd, learning,
  checkpoint parity, all-gate admission and model quality are
  Python/experimental obligations, not `refl`.
- **F07–F08 error transport (OPEN)**: prove the
  layerwise norm/error inequality
  `e(i+1) <= Lip(S(i))*e(i) + delta(i)`,
  telescope the exact products, then derive a
  same-target logit CE bound using existing norm/real-analysis owners.
  No fabricated teacher/student Lipschitz constants.
- **F09–F10 history and consumer**: reuse
  `everyExpertReopensSharedCanonical`,
  `LeechJointStateConsumerQuotientExact` and
  `ConsumerQuotientBaseChangeExact`; decode/corrections and
  selected-history authority remain separate.
- **F11–F12 distributed/semantic**: HMAC verify is not
  crash-durable exactly-once execution; independent labelled
  2x2x2 cube target correctness and common-probe triadic
  difference are not causality or argument semantics.

User workstation evidence, Python regression execution,
source-written Agda theorem and Agda kernel certification must stay
**four separate receipt classes**. Current Agda PR #1442
kernel status for this tranche remains **not executed**, even though
the Python PR #4 regressions have passed. No ESD edits, source
renaming, import-graph replacement, analytic same-object promotion
or Ibrahim Monster 3B ownership reassignment.

**Deliverable cut:** D1 source-bound C2 receipt (user executed, local
not repo-stored), D2 layer-one causal ablations (open),
D3 global CE/KL trained candidate (open), D4 all-gates-one
teacher-free validated checkpoint (open), D5 accepted Agda
kernel/refinement receipts (open), D6 complete authenticated
real-network Pareto (open), D7 independently labelled semantic
pairs/trialectic cube (open).


## 2 November cross-repository exact source update

The authoritative C2 train-only diagnostic JSON is now embedded in
LeechTransformer PR #4 at
`docs/receipts/c2_train_only_quality_diagnosis_20261102.json`
with SHA-256
`e31dec9a6135d1e9b0a819e93947d8ebfb610491473c83e118fcbe3d58aff4fc`.
It is a user-executed 4032-target receipt, not a new model-quality
result. No saved teacher/student model file digests are claimed.

New source-written golden leaves:

- F02a `LeechOddOnlyApproximationObstructionExact.agda`:
  jointly mirrored historical-state exact fitting impossibility
  for an odd-only student against a nonodd target. F02b real
  MSE/inner-product error floor remains **open**.
- F07 `LeechLayerErrorTransportExact.agda`:
  telescoping error majorant for a finite teacher/student layer
  sequence under **explicit**, unproven-for-this-model triangle,
  scaling monotonicity and Lipschitz premises. Numeric constants
  and exact PyTorch refinement remain **open**.
- Both imported through existing
  `DASHI.Unified.LeechQualityGuardTOEBridgeExact` and existing
  TOE roots; Agda kernel not run this session.

New LeechTransformer D2 implementation:
`scripts/ablate_early_layer_quality.py`, seven actual-weight
counterfactuals plus same-probe pointwise F08 logit/NLL bound;
`tests/test_early_layer_quality_ablations.py`. Focused D3
training via `student_only_layers` and `--focus-layers`
keeps the nonselected dense fallback, freezes nonselected MoE
parameters and categorically forbids false full-model promotion.
Exact commands and all remaining D1–D7 gates reside in
`docs/early_layer_quality_rescue_maxcut_20261102.md`.

Remaining: D2 test execution and actual saved-weight receipt;
D3 trained focused/global CE recovery; D4 full-gate
teacher erasure; F02b/F08 real analytic proof, F07 concrete
constants and Agda kernel; D6 actual network, D7 labelled
semantics. Original Kornienko and DASHI owners unchanged.


### 2 November D2/D3 steelman executable closure

LeechTransformer PR #4 now also includes:
`scripts/prepare_train_only_development.py` and tests,
which consume the trusted original one-document-per-window
train preparation, verify its saved train-array digest,
and create disjoint fit/development arrays WITHOUT reading
the independent final heldout. It records selected row
indices and cryptographic hashes.
`scripts/train_early_layer_dense_control.py` and tests,
which train one ordinary dense GELU FFN with parameter count
within 2*d_model+1 of the signed MoE + even student,
keeping the rest of the source transformer frozen.
This is an original-model teacher-input MSE plus full
CE/KL training control, not geometric proof or full
teacher-free student acceptance.

The constrained MoE competitor uses existing
`train_guarded_moe_continuation.py --focus-layers 1`
(or 0 / 0 1), with dense fallback elsewhere and
unconditional refusal to call any focused run
a complete teacher-free checkpoint. Both candidates
must use the same fit/development rows, learning rate,
epochs, random seed and evaluation procedure.
Parameter matching ALONE is not FLOP/time matching.
No user-local experiment results have yet been run for
these new implementations. Exact source filenames and
run commands are in
`LeechTransformer/docs/early_layer_quality_rescue_maxcut_20261102.md`.


## 3 November 2026: negative matched layer-one quality comparison

The user's **executed, train-only development** comparison
(three epochs, same reported seed/CPU, nearly identical trainable
parameter count) gave dense teacher CE **2.513**, guarded
focused-C2 hybrid **2.486**, strict C2 layer-1 student **2.833**,
and ordinary dense single-layer GELU control **2.191**.
C2 odd+even has **1,185,606** trainable parameters versus
**1,185,413** in the dense control (193 difference).
The dense control wins by **0.642 nats** against strict focused
C2. The guarded 0.5 gate retains original dense FFN weights
and compute; its 2.486 score does NOT certify teacher erasure,
standalone MoE quality or network Pareto.

**Status correction:** D2 source/ablation and D3 focused training
have user-executed measurements, but D3 *quality-superiority gate
FAILS* for this trained candidate. D4 full 12-layer teacher-free
promotion stays OPEN; D6 remote codec/transport and D7 semantic
quality should not inherit any quality-win assertion. Existing
Golden F02a and F07 are conditional/algebraic properties, not
certificates of learned quality or a measured E8 advantage.

**Steelman caveat from exact source review:** The historical
C2 focused trainer internally withheld a calibration partition,
while the ordinary dense control trained over all supplied fit rows.
It also optimized extra hybrid CE/KL terms and averaged local
loss over all layers, unlike the dense control's single-layer
local MSE + direct CE/KL. Thus matched parameters, seed, epochs
and CPU are not identical optimizer data/loss contracts. The
observed negative ranking stands for the tested procedures,
but should not be construed as a causal falsification of
all history/signed/E8 student architectures.

The original code path remains untouched by default.
LeechTransformer PR #4 adds an opt-in
`--matched-control-objective` with one focused layer and
`--export-optimizer-fit-ids`: directly match the focused
student-only local MSE + next-token CE + logit KL, revoke
previous calibration gates before each training epoch and
export the actual C2 optimizer rows for the dense control.
This source was written **after** the reported negative
experiment. It has not been newly executed or verified in
the GitHub connector session. The concrete rerun instructions
are at `LeechTransformer/docs/early_layer_quality_rescue_maxcut_20261102.md`.
The comparison remains limited by different initializations,
FLOPs, memory, routing and one-seed uncertainty; measure those
instead of asserting a universal prior advantage.

Original model provenance and attribution: Anatolii Kornienko
(Leech-LILA; DOI 10.5281/zenodo.18784424), independent
DASHI/C2/E8 owners as already cited, Ibrahim's Monster
ownership unchanged. No ESD edits, postulates or theorem
reclassification. The local JSON files are not available
through this connector, so these scores are the user's
reported results rather than independently parsed artifacts.


## 3 November 2026 — uploaded source-backed D3 result and GFX803 Nix admission

The two **uploaded** (not guessed) matched-objective CPU training
receipts are committed unchanged in LeechTransformer PR #4:
`docs/receipts/c2_focused_matched_loss_20261103.json` and
`docs/receipts/c2_dense_matched_loss_control_20261103.json`.
Their teacher/student checkpoint identities and *exact exported
optimizer training-window file hash* agree. Development scores
for 45 fit rows and 13 dev rows (819 next-token targets) are:

| Source model / execution | CE, nats |
| --- | ---: |
| Frozen dense | 2.5132008088 |
| C2 guarded hybrid, alpha=.5 | 2.5158496153 |
| Strict focused layer-1 C2 | 2.8918613345 |
| Strict all-layer student-only C2 | 11.5599299653 |
| Matched dense GELU control | **2.2160529764** |

Difference strict C2 minus matched dense control =
**+0.6758083581 CE nats**. The hybrid is *worse*
than frozen dense by 0.0026488 CE nats on this train-derived
development partition, yet remains calibration-admitted with
its original dense FFN retained. No teacher erasure or
C2 quality/efficiency win. Original model: Anatolii Kornienko
(Leech-LILA). Attribution and theorem owner boundaries unchanged.

The user correctly recalled a separate existing Nix runtime:
`chboishabba/gfx803_compat_graph/gfx803_flake_v1`.
It contains frozen ROCm 6.4 Python/PyTorch old-HSA/HIP control
and a diagnostic upgrade shell with Cachix artifacts. Its
historical Leech GPU numerical correctness verdict is
**negative** despite successful GPU enumeration; some
runs also trigger long async host resets. LeechTransformer
now adds `scripts/gfx803_moe_gpu_gate.py` and
`scripts/run_gfx803_moe_nix.sh` (plus CPU-only source
tests), reusing that Nix+host-docker-python runtime with
a fail-closed check of the REAL saved Leech teacher/student
checkpoints, full actual training token window, intra-GPU
repeatability, matched-objective gradients and one AdamW
update before any `--device cuda` training run.
Exact instructions/limitations:
`docs/gfx803_gpu_training_admission_20261103.md`.

**Evidence boundaries:** Nix shell source exists; physical
GPU parity pass does NOT exist in this conversation.
This new source has not been run on the user's hardware.
`torch.cuda.is_available` alone cannot promote
numerical correctness. A single-step pass cannot
prove long-duration reset safety, speedup, token-quality
success or the full student D4 criterion. The model's
GPU optimization remains contingent on per-workload
admission; CPU remains the verified quality reference.
The existing Golden Agda `GFX803CompatibilityReceiptExact`
already describes the query-indexed visibility/correctness
separation; no new Agda machine-check acceptance claimed.
