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
