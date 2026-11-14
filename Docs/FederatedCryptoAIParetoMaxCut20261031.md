# Federated crypto-AI Pareto max-cut ledger — 2026-10-31

**Original mission:** cryptographically accountable, federated learned expert
execution with lower actual network and coordination cost. Codec, Leech
geometry and Agda are means, not separate endpoints.

## Hard priorities ordered by highest expected leverage

P0. **Executable correctness** — verify real branch tests and Agda kernel,
fix Python source defects, enforce packet length/layout/digest and no
silent reset of expert memory. SHA-256 is not authentication.
P0. **BIDI model/consumer definition** — exact required history and expert
state at receiver, route IDs, time/sequence, model version, action witness,
state change and potential replay. Source-to-Agda simulation required.
P1. **Network placement and local reuse** — choose local expert, remote
expert, migrate a model, reuse an admitted symmetry action or ship a
compressed activation; optimize *end-to-end* latency and useful
throughput, not only compressed bytes.
P1. **Measured codec Pareto frontier** — raw, zlib, shuffle, sign-orbit,
temporal residual, dictionary reuse, action-canonical and multiscale
codec; include all side bits and exact decode requirements.
P1. **Federated cryptographic protocol** — authenticated confidentiality,
source/authorship, nonces/replay, acknowledged state and data-dependent
length leakage; fail-closed on stale or unauthenticated history.
P1. **Genuine learned MoE** — independently learned experts, learned
top-k/weights, shared vs routed pathways, load/capacity constraints,
state persistence and federated location-aware scheduling.
P2. **Symmetry programme** — exact GELU odd/even parts, history involution,
C3 vs C2 action, 5/9 and 14/27, nine-sheet/18/27 hypervoxels,
jet/fibre joins, genuine Leech rather than QR placeholder.
P2. **Grokking and safety experiments** — primary-source Kornienko
training observations, geometric loss and rank, orientation dynamics,
held-out behavior and genre controls, matched seeds and training steps.
P2. **External BIDI comparisons** — DeepSeek-V3 shared/routed expert,
Kimi K3 latent MoE and state handling, without copying expert scales.
P2. **Formal programme** — abstract weighted E/k, deterministic tie
behavior, full route/output/history trace, codec byte framing,
cryptographic session admission, replay and exact consumer commutation.

## Actual changes this round

LeechTransformer PR #4:
- `scripts/federated_activation_transport.py` now requires nested
  sign-orbit layout to agree with the outer packet, and bounds decode.
- Optional `bandwidth_bytes_per_s`, `encode_cost_seconds` and
  `decode_cost_seconds` allow time-based selection while keeping
  smallest-total-packet selection as the default.
- `tests/test_federated_activation_transport.py` adds latency and
  adversarial mismatch regression cases.

DASHI Agda PR #1442:
- `FederatedExpertTransportBidiExact.agda` now defines explicit
  encoder/wire/decoder costs and exact codec/model/history admission
  witnesses. These are mathematical interfaces, NOT packet-level
  authenticated cryptographic proofs.

## Nonpromotions

The Python/Agda tests were not run against checked-out current branches
in this session. Agda has no verified theorem for SHA-256, DEFLATE,
complete real IEEE packet format, encryption, real/float top-k,
learned optimizer behavior or network execution.
The original 600-frame video benchmark is temporal-byte-residual
evidence; it is not a Leech activation or federated-WAN gain.
The current 1.0496x real-activation baseline remains unchanged.
DeepSeek/Kimi are architectural references; original Leech-LILA
ownership remains Anatolii Kornienko. ESD remains import/read-only.

## Next decisive discriminator

On actual model activations and a remote worker, compare:
A. local computation/no network;
B. remote dense tensor;
C. remote self-contained adaptive codec;
D. remote acknowledged temporal state/delta;
E. local/remote symmetry operator reuse.
Record bytes, CPU/GPU encode/decode, expert compute, RTT, retransmission,
p50/p95/p99, model quality, reconstruction parity and security gate.
Choose a policy by the Pareto frontier and provenance receipt, not
by an assumed compression factor.
