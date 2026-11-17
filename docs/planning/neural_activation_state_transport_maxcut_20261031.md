# Neural activation transport: state-aware lossless max-cut (2026-10-31)

## Source-owner and attribution

Discussion-origin architecture and inference deployment requirements: Johl Brown.
Reuse the existing DASHI video-codec owner
`DASHI.Combinatorics.TriadicVideoCodecObservationQuotient`, the
`DASHI.Codec.TriadicPAdicCodec` constructive carrier, and
`DASHI.Codec.RANSMaskSignModel` for entropy-model interfaces.
This adapter is a DASHI-owned concrete finite proof, not a claim that video
compression and neural inference are the same physical object. No ESD surface
is changed. Keep golden Agda authoritative; do not upgrade a receipt or
a model to an empirical measurement or cryptographic theorem.

## Corrected statistical premise

Never assume meaningful rates of EXACT activation repetition across tokens,
sessions or layers. Repeated activation references require actual bitwise
identity evidence and separately measured reuse rate. Stateful prediction
is NOT the same as exact activation reuse: predicting a bit vector and
transmitting its XOR residual is lossless at any prediction accuracy.

We know the program: model hash, expert/layer identifier, tensor dimensions,
dtype and canonical byte order, routing dependency graph, predictor version,
stream sequence, and any previously ACKed predictor state. These are
**schema and state**, not independently repeated packet headers.
The receiver knows the schema through the negotiated session; if not, it
must get an explicit schema update.

## Proof already constructed

`DASHI/Codec/NeuralActivationStateTransportExact.agda` gives a concrete
boolean-vector XOR codec indexed by width, and proofs:
- `xor-involutive`;
- `xorVec-involutive`;
- `decode-encode`;
- `transport-sound` conditional on equal sender/receiver context.

The imported video-codec owner requires explicit residual, side information,
deterministic decoder, and valid reuse/correction. The concrete XOR theorem
is not an entropy-coder roundtrip theorem or a proof of stream recovery.
No claims of measured compression ratio or ZKP verification are made.
This file uses Agda safe mode without postulates or metas; compiler execution
has not been performed in this connector-only pass.

## Next concrete obligations (in descending max-cut order)

1. Canonical typed byte representation for FP16/BF16/FP32 and quantised
   activations, including NaNs, signed zeros, endianness and padding.
   Prove byte-exact reconstruction of complete tensor payloads.
2. Jointly indexed stream state: model revision, layer, expert/shard, tensor
   shape, stream and sequence. State transition may use ONLY available,
   acknowledged predecessors; prove resynchronisation after packet loss,
   duplication and reordering using checkpoints and monotonically numbered
   acknowledgements. Do not assume all peers share global runtime state.
3. Predictors: zero, prior agreed activation, per-lane XOR predictor,
   byte/bit-plane filters, model-coordinate charts and causal delta histories.
   All predictors must be cheap, deterministic and bounded in state. Prove
   exact reconstruction for each; never infer low entropy from semantics.
4. Roundtrip proof for an actual entropy payload encoder and decoder.
   Compare raw, LZ4, Zstd, bitshuffle, XOR-delta+entropy and triadic/rANS,
   with explicit metadata and dictionary transmission charges. Prefer raw
   if a codec expands or exceeds its latency/energy budget.
5. Model DAG transport congruence: swapping any raw edge for a proven
   lossless transport edge preserves reference inputs to the downstream
   computation. Neural arithmetic/rounding is an independent obligation.
6. Distributed miner capability and throughput: measured sustained
   operations/sec by expert, batch, hardware, queue, thermal and proof mode.
   Keep end-to-end TPS separate from per-miner expert operations/sec.
7. Economic optimality: choose codec and local load/offload per scheduled
   graph cut, accounting for CPU cycles, compression latency, bandwidth,
   decoder availability, proof overhead and external customer revenue.
8. Per-step commitments (model-weight root, input/output commitment,
   operation identity), ZK execution relation, non-replay and payment ledger
   proof. Hash commitments alone cannot establish arithmetic correctness.
   The postulated `Verification.ZK` contract is NOT a kernel proof.
9. Counterexamples: exact activation reuse absent; predictor worse than raw;
   state desynchronisation; path-local saving harms global critical path;
   proof overhead exceeds work value; new miners lower unit revenues.

## Measurement contract

For each observed activation stream record: stable stream identifier,
schema version, canonical tensor bytes before/after encode, causal
references actually available at receiver, raw and encoded byte counts
including amortised headers, encode/decode time, final bitwise equality,
network p50/p95/p99, task queueing, sustained expert ops/sec and power.
Compare at equal model weights and arithmetic precision.

A correct lossless codec can have a 1.0x or worse compression ratio.
An optional reference/entropy coder can only be claimed to save traffic
after measured evidence. The goal is *fewer paid bytes on expensive edges
at admissible cost*, not compression for its own sake.

## Integration boundary

This branch intentionally does NOT edit the giant existing TOE imports before
the new Agda typechecks. Once checked, attach it using the repository's
existing `DASHI/Unifier.agda` and
`DASHI/EverythingTOESymmetryResolved369.agda` import spine without
overwriting newer source changes.
