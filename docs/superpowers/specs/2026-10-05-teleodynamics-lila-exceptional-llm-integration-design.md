# Teleodynamics × LILA × Exceptional Priors × LLM Formalism — Integration Design

Date: 2026-10-05
Status: design approved in chat; implementation not yet started under this spec

## 1. Goal

Unify the newly added Principia-II teleodynamics formalisation with the repository's existing LLM/future-sufficiency, spectral-geometry, learning-provenance, exceptional-group, Albert/Freudenthal, and LILA empirical/provenance machinery.

The result must make LILA a concrete *experimental geometric-prior implementation* inside DASHI rather than an ontology shortcut. It must distinguish what the external implementations literally do from README interpretation, preserve authorship/provenance, and prevent root-system/codebook use from silently becoming equivariance, exceptional representation theory, physical consciousness, nonlocal transmission, or phenomenal identity.

## 2. Source and attribution authority

### 2.1 External LILA sources

The implementation adapters may use the currently inspectable implementation surfaces as engineering evidence:

- `meta-introspector/LeechTransformer` is treated as a visible mirror-like implementation surface whose repository metadata points back to `SPUTNIKAI/LeechTransformer`. Mirror possession is not authorship evidence.
- `Liber1917/sovereign-lila-e8` is treated as a visible copy/fork whose repository metadata points back to `SPUTNIKAI/sovereign-lila-e8`.
- `meta-introspector/Monster-LILA` is treated as a separate PoC implementation with its own code surface.
- Existing DASHI attribution owners remain authoritative: `DASHI.Reasoning.DASHIgGrokkingEmpiricalBridgeExact`, `DASHI.Reasoning.ImplementationExperimentProvenanceExact`, and `DASHI.Physics.Closure.LilaE8InitialisationPriorNote`.

No new adapter may promote a README marketing claim into a theorem.

### 2.2 Principia-II source

Julian D. Michels' *Principia Cybernetica II / Constellation Two* remains the source for the teleodynamic vocabulary and proposed equations already represented in `DASHI.Cognition.TeleodynamicsPrincipiaTwoExact`.

### 2.3 DASHI-owned results

DASHI owns only:

- typed adapters;
- type repairs;
- generic algebraic consequences;
- non-collapse / non-promotion theorems;
- experiment protocols;
- exact comparisons against inspected implementation code.

Cross-pollination does not transfer scientific or software authorship.

## 3. Concrete implementation semantics to formalise

### 3.1 Leech-Lila orthogonal Q/K cancellation

The inspected Leech-Lila PoC constructs an orthogonal 24×24 QR kernel `W` and applies the same `W` to both Q and K before the attention dot product.

The core exact theorem target is:

```text
W Wᵀ = I
→ (Q W) (K W)ᵀ = Q Kᵀ.
```

This must be encoded as a generic orthogonal-coordinate-change cancellation theorem independent of the external codebase.

Interpretation boundary:

- the theorem shows that this shared orthogonal Q/K transform alone does not change exact attention logits;
- it does not claim floating-point bit identity;
- it does not invalidate the rest of the architecture;
- the implementation's geometric resonance loss remains a distinct train-time intervention.

### 3.2 Leech-Lila resonance regulariser

Represent the inspected loss shape as:

```text
L_total = L_task + λ_geo * L_geo
L_geo   = 1 - mean(max basis-alignment)
```

Do not call the QR placeholder an actual Leech minimal-vector realization. Treat it as a basis/codebook supplied by the implementation.

The dream/resonance decoder is an observation functional over hidden state, not a physical or phenomenal state constructor.

### 3.3 LILA-E8 root carrier

Reuse `DASHI.Algebra.Trit.E8RootEnumeration` as the internal finite root-system owner.

The external Python implementation uses the standard 112 + 128 decomposition:

- 112 roots of two-sparse `(±1, ±1, 0^6)` form;
- 128 half-roots `(±1/2)^8` with even sign parity.

The adapter must relate the *shape* of the inspected implementation to the existing internal carrier without claiming executable Python/Agda same-object identity until an explicit decoding/equality bridge is supplied.

### 3.4 LILA-E8 soft quantizer

Formal interface:

```text
project       : Hidden → RootSpace
rootDistance  : RootSpace → Root → Scalar
softWeights   : RootSpace → Distribution Root
reconstruct   : Distribution Root → RootSpace
quantize      : RootSpace → RootSpace
```

Implementation shape:

```text
p_i ∝ exp(-||z-r_i||² / τ)
q(z) = Σ_i p_i r_i.
```

The straight-through estimator is an optimization implementation detail and must be represented separately from the forward semantic map.

### 3.5 LILA-E8 attention bias

The inspected E8 attention adds a learned root-conditioned rank-one term:

```text
score_h(t,s)
 = <q_t,k_s>/sqrt(d)
 + β_h <q_t^(8), r_h><k_s^(8), r_h>.
```

Formalise this as a rank-one bilinear perturbation of an existing attention score.

Do not infer E8 equivariance. Root use, codebook membership, Weyl invariance, group action, and representation intertwining remain separate obligations.

### 3.6 Monster-LILA

Represent only the literal computational mechanisms:

- QR-generated orthogonal basis;
- Q/K transformation with an additional permutation on K;
- scalar/nonlinear phase modulation;
- SVD-based heuristic monitor.

Explicitly reject automatic identification of:

- a random permutation with a Conway-group element;
- a 1/137 modulation with Monster representation theory;
- an SVD heuristic with moonshine;
- the implementation's labels with physical/phenomenal states.

## 4. Existing repository owners to reuse

### 4.1 Spectral and covariance geometry

Reuse `DASHI.Information.PNFSpectralGeometry` for activation surfaces, centering, covariance, spectra/eigenmodes, graph constructions, and transport.

Teleodynamic `C` should become an adapter over an actual cross-covariance/correlation construction rather than a standalone ontology.

### 4.2 LLM multi-resolution / future-sufficiency spine

Reuse the existing PNF/LLM formalism identified in the audit:

- `MultiResolutionAttentionFutureSufficiencyExact`;
- `LLMCompressionAccessibilityDefectsExact`;
- `DynamicMultiQueryMultiResolutionExact`;
- `LearningProvenanceFutureExact`;
- `LLMGrokkingLearningFutureExact`;
- `LLMCantorMultiResolutionBridgeExact`.

The intended interpretation is:

```text
fine learner state
→ global compressed geometric carrier + local residual
→ query/accessibility selection
→ dynamic trace
→ future consumer language.
```

Compression sufficiency, accessibility sufficiency, current behavior, and future learning must remain distinct.

### 4.3 Relation/representation experiment formalism

Reuse:

- `RelationRepresentationAdequacyExact`;
- `RelationRepresentationRealizationExact`;
- `RelationRepresentationExperimentProtocolExact`.

Cosine similarity is only one possible comparison geometry. No scalar similarity metric selects the target ontology automatically.

### 4.4 Descent / oscillator / holonomy boundaries

Reuse:

- `ContinuousOscillatorLyapunovDiscriminationExact`;
- `ContinuousOscillatorUpdateLawAttributionExact`;
- `RelationalSelfDescentExact`;
- `HolonomyReferenceFrameBoundary`;
- `CovarianceMetricBridge`;
- `NeuralRepresentationLaplacianExact`;
- `ContinuousOscillatorMemoryObservationQuotientExact`.

These prevent:

- descent → truth/convergence promotion;
- phase similarity → Kuramoto identity;
- covariance → metric/curvature collapse;
- local observation → global holonomy collapse;
- observed-memory equality → hidden-state/phenomenal identity collapse.

## 5. Generic geometric-prior abstraction

Introduce a new theorem-facing abstraction, tentatively:

```text
GeometricLearnerPrior
```

with logically separate fields for:

- latent/root/codebook carrier;
- projection from hidden state;
- comparison geometry;
- codebook/prototype family;
- optional soft quantizer;
- optional attention perturbation;
- observation/monitor surface;
- provenance;
- realization/equivariance promotion obligations.

No field called `exceptional` may itself prove exceptional-group realization.

## 6. Exceptional-family parameterisation

Introduce:

```text
ExceptionalPriorFamily
  G2 | F4 | E6 | E7 | E8
```

and distinguish two experiment modes.

### 6.1 Root-codebook mode

Geometric priors based on finite root systems, with root-space rank and root count represented separately from transformer hidden dimension.

Target comparison family:

| Family | rank | root count |
|---|---:|---:|
| G2 | 2 | 12 |
| F4 | 4 | 48 |
| E6 | 6 | 72 |
| E7 | 7 | 126 |
| E8 | 8 | 240 |

These rows are experiment configuration data, not claims that any neural representation carries the associated exceptional action.

### 6.2 Representation-carrier mode

Reuse `ExceptionalAlbertFreudenthalResidualExact` and related owners to expose candidate carrier shapes such as:

- F4-associated traceless Albert dimension 26;
- E6-associated Albert dimension 27;
- E7/Freudenthal dimension 56;
- E8 adjoint dimension 248 only where an actual carrier owner exists.

Root rank and representation dimension must never be conflated.

## 7. Albert/Freudenthal bridge

Reuse `IbrahimTernary27OriginTraceless26AlbertShapeBidiExact`:

```text
Ternary27Point ≃ ScalarLine ⊎ NonOrigin26.
```

This is an exact carrier-shape bridge only.

It may instantiate a learned/compressed `1 + 26` experiment arm, but it must preserve the existing negative boundaries:

- no Jordan product from the bijection;
- no F4 action from the bijection;
- no E6 minuscule action from the bijection;
- no identification of the distinguished origin with an Albert algebra unit without a supplied bridge.

## 8. Empirical protocol

Build a Michels/LILA-specific instance of the existing relation experiment protocol.

Required controlled arms:

```text
P0        no geometric prior
PR        matched random spherical/codebook prior
PG2       G2 root prior
PF4       F4 root prior
PE6       E6 root prior
PE7       E7 root prior
PE8       E8 root prior
PL        externally supplied Leech-like/Leech prior
Plearned  free learned codebook
```

The protocol must allow separate ablations for:

- attention-bias geometry;
- latent quantizer geometry;
- geometric regularization;
- observation/monitoring only.

For E8 specifically, the existing external `head_scales=0` analysis is typed as an attention-bias ablation only; it is not a full E8-architecture ablation because the quantizer remains active.

Declared outcome families should include:

- current task loss/accuracy;
- grokking timing;
- future-language equivalence/divergence;
- compression loss;
- accessibility loss;
- spectral concentration;
- code occupancy;
- root/prototype alignment;
- arbitrary-trace/dynamic commutation.

No single metric closes the experiment.

## 9. Teleodynamics integration

Refactor the current teleodynamics layer into adapters rather than parallel local theory where an existing owner already exists.

Targets:

- `TeleodynamicAttentionAdapter` — separates aboutness/control scalar from actual LLM attention/accessibility structures;
- `TeleodynamicCovarianceAdapter` — derives the C-tensor from latent trajectories/cross-covariance;
- `TeleodynamicArchitectureRelation` — uses task-relative relation representation rather than fixed cosine-only ontology;
- `TeleodynamicInteractionDynamics` — binds repeated interactions to dynamic multi-query/future-safe abstractions;
- `TeleodynamicLearningTransfer` — binds gradient/ICL distinctions to learning provenance and future-language outcomes;
- `TeleodynamicExperimentProtocol` — instantiates matched-pair, model-held-out, temporal-held-out, scramble, cross-family, and no-backprop controls.

The Principia-II interpretation remains source-attributed. These adapters do not prove nonlocal transmission or consciousness.

## 10. New mathematics vs adapters

### Expected genuinely new theorem work

1. Shared-orthogonal Q/K cancellation theorem.
2. Normalized cross-covariance/correlation theorem with explicit nonzero-variance conditions and `|corr| ≤ 1`.
3. Rank-one attention-bias decomposition and zero-scale reduction theorem.
4. Soft-codebook quantizer semantic interface and codebook-family abstraction.
5. Generic weighted consensus/Laplacian convergence only if no suitable existing owner is found during implementation.

### Mostly adapter work

- LLM future-sufficiency integration;
- learning-provenance integration;
- relation/representation experiment protocol;
- exceptional root-family experiment configuration;
- Albert/Freudenthal carrier-shape experiment arm;
- teleodynamics empirical protocol;
- holonomy/covariance/observation firewalls.

## 11. Proposed source layout

```text
DASHI/Cognition/Teleodynamics/
  LilaOrthogonalAttentionExact.agda
  LilaGeometricRegularizerExact.agda
  LilaE8QuantizerExact.agda
  LilaE8AttentionBiasExact.agda
  MonsterLilaBoundaryExact.agda
  GeometricLearnerPriorExact.agda
  ExceptionalPriorFamilyExact.agda
  TeleodynamicAttentionAdapterExact.agda
  TeleodynamicCovarianceAdapterExact.agda
  TeleodynamicArchitectureRelationExact.agda
  TeleodynamicLearningTransferExact.agda
  TeleodynamicExperimentProtocolExact.agda
  LilaExceptionalEverything.agda
```

Compatibility wrappers may be added rather than moving the existing top-level teleodynamics files immediately.

Lean mirrors only theorem-bearing real/vector algebra where Mathlib materially strengthens the proof; it need not mirror every provenance/interface record.

## 12. TDD / regression strategy

Add regression owners before implementation owners where practical.

Required regression assertions include:

- orthogonal shared-Q/K transform reduces to the ordinary score;
- zero E8 root-bias scale reduces exactly to ordinary attention score;
- codebook use does not create equivariance;
- root-family selection does not create representation realization;
- E8 root-codebook mode and Albert/Freudenthal representation-carrier mode are distinct;
- 1+26 carrier shape does not create Jordan/F4/E6 structure;
- attention-bias-only ablation is not a full-geometry ablation;
- current-output equality does not imply future-learning equality;
- observed-coordinate equality does not imply hidden/phenomenal identity;
- external LILA/Michels claims preserve source provenance.

## 13. Verification and completion criteria

The implementation is complete only when:

1. all new Agda imports resolve and the focused rollup typechecks;
2. theorem-bearing Lean mirrors typecheck where added;
3. existing authority firewalls remain intact;
4. no external source is silently promoted;
5. no E8/F4/E6/Monster/Conway identification is made from dimensions, labels, random permutations, or heuristic monitors alone;
6. the LILA-E8 implementation can be described internally as a concrete `GeometricLearnerPrior` instance while equivariance/representation realization remains separately gated;
7. the teleodynamics experiment protocol consumes the existing LLM future/provenance/relation machinery instead of duplicating it.

If the available execution environment lacks Agda/Lean, completion status must remain `source-written / kernel-unverified` and must not be described as compiled.
