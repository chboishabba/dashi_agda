# Federated crypto-AI network max-cut: codec learning → expert transport

## Original objective restored

The user objective is federated/distributed cryptographic AI inference over
network-constrained peers, NOT improving compression as an isolated goal.
The network cut is activation, Q/K/V, expert dispatch, history state and
checkpoint/version continuity under bandwidth, RTT, packet loss and peer
availability limits. The codec may reduce bytes but adds CPU/GPU encoder
time, decoder time, metadata and possible routing synchronization.
Acceptance metric: end-to-end useful tokens/s and p95/p99 latency at
identical model quality and state, not only compression ratio.

## Reuse of actual sibling work

- `dashitest/video_bench_reuse.py`: canonical representative under C2
  signed-trit block inversion; carry action witness.
- `dashitest/scripts/gen_codec_E_seq.py`: magnitude-only diagnostic
  cannot reconstruct state without a sign witness.
- `DASHI/Combinatorics/TriadicVideoCodecObservationQuotient.agda`:
  deterministic decode, signed residual, admitted reuse, side-cost.
- `DASHI/Compression/TriadicCodecBoundary.agda` and
  `Docs/TriadicCompressionEvidenceBoundary.md`: 600-frame
  byte-valued temporal-residual result, NOT triadic entropy proof.
- `DASHI/Interop/DistributedEpistemicPlaneSeparationExact.agda`:
  transport/reconciliation and authority are distinct concerns.

## Now implemented, source-level only

`scripts/federated_activation_transport.py` selects among complete
**raw**, **zlib**, and **sign-orbit + zlib** packets based on total bytes,
including metadata. The packet specifies model revision, *history*
revision, float itemsize, 24-element block layout, original length,
and SHA-256 of original bytes. Decoder rejects stale references,
unknown layouts, bad digests, malformed compressed streams and
declared outputs exceeding receiver's size budget.
`scripts/ieee_sign_orbit_codec.py` implements bit-exact sign XOR,
not numerical negation, to preserve signed zero/NaN payload bits.
`tests/test_federated_activation_transport.py` specifies exact
roundtrips, adaptive raw fallback and stale-state rejection.
`benchmark_ieee_sign_orbit.py` allows inputs from real saved tensors.
These programs are COMMITTED; this turn has not run exact-branch tests
against a checked out GitHub tree.

The Agda companion
`DASHI/Reasoning/FederatedExpertTransportBidiExact.agda`
is a finite admission/rejection skeleton with model+history
revisions and routed witness. It does NOT establish SHA-256, zlib,
packet framing or the Python implementation's byte-level simulation.

## Federated and crypto threat/latency controls

Compression must happen *before* authenticated encryption, not on
ciphertext. SHA-256 here is an accidental-corruption/equality check,
**not authentication**: an untrusted peer can replace both digest
and payload. The production receiver requires authenticated encryption
or signature binding packet metadata, model revision, history revision,
selected expert IDs, action witnesses and sequence number.
Prevent replay, cross-session history confusion and out-of-order state
updates with signed session/monotonic sequence contracts.

**Compression side channels:** packet lengths can leak information if
secret and attacker-controlled data share a compression context.
Do not enable data-dependent compression for secret-bearing mixed
contexts by default. Provide explicit policy / padding and leakage
tests, otherwise choose raw encrypted transport.

If a remote peer does not share an ACKed exact historical state,
a residual-only packet is invalid. Send a complete independently
decodable packet or negotiate/ack a versioned reference, with loss
recovery and replay. A hash is not a state synchronization mechanism.

## BIDI and empirical comparator

Capture actual LeechGPT per-layer tensors and route logs.
For each consumer: the sender proposes packet (codec, revision,
expert IDs, orientation, correction); receiver either verifies
state and byte identity or rejects. Compare full-packet raw/zlib,
shuffle, sign-orbit, and measured history-indexed temporal deltas.
Account for all bytes including keys/nonces/tags, ACKs/retries,
checkpoint transfer, expert placement and header overhead.

Use a network simulation sweep for (bandwidth, RTT, packet loss,
expert host placement, encoder/decoder cycles), with:
  total latency = encode + queue + serialized_bytes/link_bandwidth
                  + network RTTs + decode + expert_compute
                  + downstream transport.
One size result cannot establish p95 latency or actual WAN gain.

DeepSeek-V3 and Kimi K3 are MoE BIDI competitors for learned routing,
load balancing and placement; their expert counts are not target sizes.
The specific winning outcome is lower end-to-end latency/bytes at
noninferior held-out quality without violating cryptographic policy.

## Gate status

- Versioned self-contained lossless wire candidate: source-written.
- Adapter into actual remote worker/cryptographic transport: OPEN.
- Tests, real tensor captures, packet-loss trials and cryptographic
  integration: NOT EXECUTED/OPEN.
- Agda finite wire admission: source-written, KERNEL UNCHECKED.
- Full Python/Agda/wire/crypto bisimulation: OPEN.

Original Leech-LILA credited to Anatolii Kornienko; DASHI/sibling
codec and federated work retain their original source ownership.
No ESD surface was modified.
