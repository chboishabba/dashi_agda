# Federated geometric learned-MoE: canonical full problem and repository weave

**Date:** 2026-10-31. **Formal owner:** `DASHI/Reasoning/FederatedGeometricLearnedMoEProblemExact.agda` on Agda PR #1442. This document is the full problem statement, not a declaration that every field is implemented or verified.

## Statement of the experiment

For each time t, joint state z_t=(x_t,H_{1,t},...,H_{E,t},K_t,V_t, model revision, routing/provenance) determines a learned expert set S_t=TopK(r_θ(z_t)), normalized weights w_{e,t}, expert-specific nonlinear outputs F_{θ,e}(x_t,H_{e,t}) and recurrent state transitions U_{θ,e}. The selected outputs mix; **unselected histories persist**. For a proposed action a on this historical carrier, record its full expert-ID permutation, route/weight changes, output involution and state transition (or exact corrective residual). No claim follows from the action being called 'negative'.

A semantic intervention s (Sophontic paired counterfactual) and a geometric action a are *different typed objects*. Fitted correspondence requires actual source and downstream consumer observations, decoder and composition compatibility, and held-out tests. Opposite arguments are not automatically negation or geometric antipodes. Opposite sign is not an ethical label.

Define the remote consumer C. Two representations z,z' are admissibly equivalent only when C(z)=C(z') **with the consumer's historical dependencies included**, or the receiving decoder reconstructs z exactly. For signed or hypervoxel quotient q, prove q(I z)=I_q(q z) AND its decoding/corrective witness; matching fibre/cardinality/fingerprint is insufficient. A claimed network saving must include the action witness, state version, selected expert IDs, coder model, correction, crypto framing, ACK, retransmit and compute/runtime costs. An unacknowledged remote history is not a shared baseline.

For link bandwidth B, RTT L, selection/placement π and candidate strategy a:
  T(a)=T_local_compute(a)+T_encode(a)+8·wire_bytes(a)/B
       +network_round_trips(a)·L+T_decode(a)+T_remote_compute(a)
       +T_ack/recovery(a)+T_queue(a).
Constrain quality, reproducibility, exact consumer reconstruction, authorized provenance, and state synchronization. Minimize Pareto objectives (p50/p95/p99, throughput, bytes, compute and correctness), rather than asserting one codec is always optimal. 1 Gbit/s=125 MB/s, 10 Gbit/s=1250 MB/s; 1 MiB serialization 8.389 ms/0.839 ms. Actual RTT is distinct and can dominate isolated expert calls.

## Existing canonical owners we are **reusing**, not replacing

### Base-3, C2, C3, 369 and high-rank fabric
- `DASHI/Foundations/BalancedTernaryAntipodal369OrbitHierarchyExact.agda`: (3,9,27) -> (2,5,14) classes; fixed centre plus 1,4,13 antipodal pairs. The 27 carrier is 13*2+1. No literal model expert/Monster correspondence inferred.
- `DASHI/Foundations/TernaryHypervoxelPermutationTransportExact.agda`: exact recursive S3 address permutation, commuting with push/pop and joins; distinguishes diagonal action from full wreath automorphism.
- `DASHI/Foundations/RecursiveRadixHypervoxel.agda`, `DASHI/Foundations/BalancedTernaryAntipodalOrbitExact.agda`: existing p-ary address and signed-orbit carrier.
- `DASHI/Moonshine/C3FourierConjugationExact.agda`, `DASHI/Moonshine/JInvariant369ReflectionEquivarianceExact.agda`: C3 Fourier conjugation vs distinct C2 inversion, concrete reflection and observer commuting-square obligations. Riemann/zeta analogy stays orbit-shape unless same-object identification is separately proved.
- Existing jet/hyperfabric/fibre join models remain donors; do NOT invent stand-ins for their exact geometric information.

### Consumer descent, temporal/history and exact codec
- `DASHI/Core/ConsumerQuotientBaseChangeExact.agda`: fibre constancy criterion and commuting base-change, a real *consumer-relative* basis for admissible quotient.
- `DASHI/Reasoning/LeechSignedHistoryExpertBidiExact.agda`, `LeechLearnedOrbitMixtureBidiExact.agda`, `LeechWeightedHistoryMoEBidiExact.agda`: state involution, selected expert identities and finite 2-expert weighted mixture. Only the respective finite claims are established in source, not real softmax/optimizer correctness.
- `DASHI/Combinatorics/TriadicVideoCodecObservationQuotient.agda` and `DASHI/Compression/TriadicCodecBoundary.agda`: signed residual, deterministic decoder, side bits and *temporal byte* evidence classification. The reported 600-frame 0.032 bpp is a byte-residual+zlib result, NOT proof of triadic entropy or Leech compression.
- `DASHI/Reasoning/IEEEOrbitSignWitnessBidiExact.agda` and `DASHI/Reasoning/FederatedExpertTransportBidiExact.agda`: finite sign-bit/wire admission models; not a verified zlib/AEAD/IEEE framing proof.

### Semantic/Sophontic, learning and non-antipode
- `DASHI/Core/ArgumentResponseNonGeometricOppositeBidiExact.agda`: objections, evidence challenges, alternative explanations, qualified agreement and suspension are not geometric antipodes.
- Agda PR #1094 and #1095: Sophontic semantic-intervention equivariance, decoded representation compatibility, action fitting/composition, E8/Monster geometry candidate discrimination and surface+dependent residual exact reopening.
- Agda PR #1265: Sophontic × Dust/Noise forward-only credit and Walsh paired experiments; finite synthetic results do not imply trained Leech specialization or semantic sign inference.
- `DASHI/Reasoning/LeechExpertSignNonAntipodeBoundaryExact.agda`: independent semantic response, geometric action and outcome types; counterexample distinguishes response category and chart sign.
- Exact GELU(x)=x/2+x/2 erf(x/sqrt2). This analytic parity identity does not make learned expert FFNs or selected mixtures automatically equivariant.

### Federation, crypto, and authority
- `DASHI/Interop/DistributedEpistemicPlaneSeparationExact.agda`, `DASHI/Interop/ITIRFederatedTypedWorldProjectionExact.agda`, `Docs/roadmaps/ITIRFederatedTypedWorld20260920.md`: authority/provenance/history/transport separation, content-addressed source and consumer, no promotion from transport receipt to semantic truth.
- `LeechTransformer/models/history_orbit_moe.py`: real independently parameterized PyTorch networks; default-off LeechGPT integration is in PR #4.
- `LeechTransformer/scripts/federated_activation_transport.py`, `ieee_sign_orbit_codec.py`, `federated_five_strategy_pareto.py`: packet and arithmetic prototypes, not distributed encrypted runtime.
- DeepSeek-V3 and Kimi K3 are separately authored modern learned top-k/shared/latent MoE engineering comparators, not mathematical ownership of our symmetry or source of safe/unsafe labels.

## Exact proof obligations and non-promotions

| Gate | Exact requirement | Current class |
| --- | --- | --- |
| Model | E,k generic, distinct learned parameters, sparse routing, normalized weights, selected-only history transition, stable full trace | Interface + restricted finite Agda; full bridge OPEN |
| Training | source optimizer/training step, gradient/forward-only credit and observed specialization | OPEN |
| Geometry | actual group action on learned tensors+histories, state/route permutation, weight equivariance, residual if failure | conditional interface OPEN |
| Semantics | paired Sophontic evidence, semantic↔geometry action fit, decoder/consumer compatibility | previous owners reused, full model OPEN |
| Numerology | 3/9/27 fixed/paired orbit cardinalities, 5/9 and 14/27, recursive hypervoxel join | finite owners; identification with learned networks OPEN |
| Codec | byte-exact compression, signed orbit witnesses, serialized packet, deterministic decoder, full side cost | Python source and finite Agda partial, end-to-end formal bridge OPEN |
| Federation | state ACK, scheduling, local/remote choices, failures, retries and real bandwidth/latency | cost model only OPEN |
| Crypto | authenticated transcript, replay safety, privacy side channels, provenance, authorization | abstract boundary OPEN |
| Evaluation | 1/10 Gbit numerical model, actual activation captures, five-strategy comparison, quality/safety tests | arithmetic; real test OPEN |
| Verification | kernel-checked Agda, executable Python regression, cross-language refinement | NOT VERIFIED HERE |

**Absolute prohibition:** count matches, character fingerprints, sign symmetry, geometric opposites or synthetic receipts do not prove a physical model, Monster module, Riemann zeta same-object relation, ethical polarity or learned expert action. No ESD source modified; original sources/authors attributed by domain.
