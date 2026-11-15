# Teleodynamics × LILA × Exceptional Priors × LLM Formalism Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Implement the approved teleodynamics/LILA/LLM/exceptional-prior integration as provenance-bounded Agda owners and a mirrored Lean theorem surface where the existing PR already has corresponding abstractions.

**Architecture:** Keep concrete external LILA semantics in small adapter modules, reuse existing DASHI LLM/spectral/learning/exceptional owners, and make every promotion obligation explicit. New mathematics is isolated from experiment-protocol and interpretation layers so source evidence, generic derivation, and open claims cannot collapse into one another.

**Tech Stack:** Agda + standard library; Lean 4 + Mathlib for mirror theorems; GitHub PR branches and existing regression/Everything aggregators.

**Spec:** `docs/superpowers/specs/2026-10-05-teleodynamics-lila-exceptional-llm-integration-design.md`

## Global Constraints

- Preserve SOURCE / SOURCE-NESTED / DASHI FORMALISATION / OPEN attribution.
- Mirror/fork possession is not authorship evidence.
- Do not promote README interpretation into theorem authority.
- Root-system/codebook use does not establish equivariance or exceptional representation realization.
- Root rank and representation dimension remain distinct.
- Carrier cardinality does not create Jordan/F4/E6/E7/E8 actions.
- Teleodynamic adapters do not establish consciousness, phenomenal identity, nonlocal transmission, or a quantum mechanism.
- Existing DASHI owners remain canonical wherever they already supply the abstraction.

## Review Focus

1. Shared orthogonal Q/K transforms must cancel only under the exact supplied orthogonality law; non-orthogonal and asymmetric transforms must not be promoted.
2. E8 attention-bias ablation at zero learned scale must reduce to the baseline score while leaving the separate quantizer untouched.
3. A finite codebook prior must not be interpreted as group equivariance without an explicit action/intertwiner witness.
4. The Albert `1+26` carrier arm must retain all current negative boundaries on Jordan/F4/E6 semantics.
5. Experiment protocols must keep current behavior, compression sufficiency, accessibility sufficiency, and future-learning equivalence as separate consumers.

---

### Task 1: Concrete LILA algebra and regression surface

**Files:**
- Create: `DASHI/Cognition/Teleodynamics/LilaRegression.agda`
- Create: `DASHI/Cognition/Teleodynamics/LilaOrthogonalAttentionExact.agda`
- Create: `DASHI/Cognition/Teleodynamics/LilaGeometricRegularizerExact.agda`

**Interfaces:**
- Consumes: generic scalar/matrix-operation interfaces supplied locally; existing attribution owners.
- Produces: `OrthogonalSharedQK`, `sharedOrthogonalQKPreservesScore`, `GeometricRegularizer`, `ResonanceObserverBoundary`.

- [ ] Write the regression module first, importing the not-yet-created owners and pinning shared-Q/K cancellation plus regularizer/observer non-promotion.
- [ ] Verify RED by checking exact-head CI/build status; record SOURCE-WRITTEN/KERNEL-UNVERIFIED if no Agda runner exists.
- [ ] Implement the minimal algebraic owner with an explicit supplied equation `qWkWT = qk` derived through an orthogonality/interchange receipt rather than floating arithmetic.
- [ ] Implement the regularizer and observer interfaces with source-code provenance and false phenomenal/Leech-minimal-vector promotion flags.
- [ ] Re-check exact-head CI/build status and commit.

### Task 2: LILA-E8 quantizer and rank-one attention bias

**Files:**
- Create: `DASHI/Cognition/Teleodynamics/LilaE8Regression.agda`
- Create: `DASHI/Cognition/Teleodynamics/LilaE8QuantizerExact.agda`
- Create: `DASHI/Cognition/Teleodynamics/LilaE8AttentionBiasExact.agda`

**Interfaces:**
- Consumes: `DASHI.Algebra.Trit.E8RootEnumeration`; Task 1 attribution conventions.
- Produces: `SoftCodebookQuantizer`, `E8RootShapeAdapter`, `RankOneAttentionBias`, `zeroScaleReducesToBaseline`.

- [ ] Write regression imports/examples first for 112+128=240 root-shape reuse, forward quantizer vs optimizer separation, and zero-scale attention reduction.
- [ ] Verify RED status.
- [ ] Implement a generic soft-codebook semantic interface, with external E8 Python same-object identity explicitly absent.
- [ ] Implement the rank-one bias interface and structural zero-scale reduction theorem.
- [ ] Add explicit false flags for E8 equivariance/Weyl invariance/intertwining unless separately witnessed.
- [ ] Re-check status and commit.

### Task 3: Generic geometric learner prior and exceptional-family experiment configuration

**Files:**
- Create: `DASHI/Cognition/Teleodynamics/GeometricLearnerPriorExact.agda`
- Create: `DASHI/Cognition/Teleodynamics/ExceptionalPriorFamilyExact.agda`
- Create: `DASHI/Cognition/Teleodynamics/ExceptionalPriorRegression.agda`

**Interfaces:**
- Consumes: Tasks 1–2; `ExceptionalAlbertFreudenthalResidualExact`; existing compact exceptional-family constructors where useful.
- Produces: `GeometricLearnerPrior`, `ExceptionalPriorFamily`, `PriorMode`, canonical root counts/ranks, representation-carrier dimensions, promotion boundary.

- [ ] Write regression first for G2/F4/E6/E7/E8 rank/root-count rows and the rank-vs-representation-dimension distinction.
- [ ] Verify RED status.
- [ ] Implement the generic prior record separating projection, codebook, comparison, quantizer, attention perturbation, observer, provenance, and promotion obligations.
- [ ] Implement exceptional root-codebook experiment rows: `(2,12)`, `(4,48)`, `(6,72)`, `(7,126)`, `(8,240)`.
- [ ] Implement representation-carrier rows only where existing owners justify dimensions; keep action/equivariance false by default.
- [ ] Re-check status and commit.

### Task 4: Albert/Freudenthal `1+26` prior arm

**Files:**
- Create: `DASHI/Cognition/Teleodynamics/AlbertPriorBridgeExact.agda`
- Create: `DASHI/Cognition/Teleodynamics/AlbertPriorBridgeRegression.agda`

**Interfaces:**
- Consumes: `IbrahimTernary27OriginTraceless26AlbertShapeBidiExact`; Task 3 geometric prior.
- Produces: a `1+26` carrier experiment arm over the exact existing ternary-27 object and inherited non-promotion theorems.

- [ ] Write regression first proving the adapter reuses the exact `Ternary27Point ≃ ScalarLine ⊎ NonOrigin26` maps while preserving all negative semantic boundaries.
- [ ] Verify RED status.
- [ ] Implement the adapter without introducing a Jordan product or exceptional action.
- [ ] Re-check status and commit.

### Task 5: LLM future-sufficiency and learning-provenance adapters

**Files:**
- Create: `DASHI/Cognition/Teleodynamics/LLMGeometricPriorBridgeExact.agda`
- Create: `DASHI/Cognition/Teleodynamics/LLMGeometricPriorBridgeRegression.agda`

**Interfaces:**
- Consumes: existing multi-resolution attention, compression/accessibility, dynamic multi-query, learning-provenance, grokking-future, and relation-representation owners; Tasks 2–4.
- Produces: `GeometricPriorCompressionAdapter`, `GeometricPriorDynamicAdapter`, `LearningTransferMode`, and explicit current/future separation receipts.

- [ ] Write regression first for compression-vs-accessibility separation, gradient-vs-context transition separation, and present-output-vs-future-language separation.
- [ ] Verify RED status.
- [ ] Implement adapters against the exact existing owner signatures found on the live branch; ledger any naming mismatch as a plan ruling rather than duplicating abstractions.
- [ ] Re-check status and commit.

### Task 6: Teleodynamic adapters and experiment protocol

**Files:**
- Create: `DASHI/Cognition/Teleodynamics/TeleodynamicAttentionAdapterExact.agda`
- Create: `DASHI/Cognition/Teleodynamics/TeleodynamicArchitectureRelationExact.agda`
- Create: `DASHI/Cognition/Teleodynamics/TeleodynamicLearningTransferExact.agda`
- Create: `DASHI/Cognition/Teleodynamics/TeleodynamicExperimentProtocolExact.agda`
- Create: `DASHI/Cognition/Teleodynamics/TeleodynamicIntegrationRegression.agda`

**Interfaces:**
- Consumes: current `TeleodynamicsPrincipiaTwoExact`; Task 5; `RelationRepresentationExperimentProtocolExact`.
- Produces: task-relative architecture relation, attention/aboutness separation, learning-transfer modes, controlled prior arms, and falsification protocol.

- [ ] Write integration regression first for scramble, cross-family, no-backprop/ICL-only, model-held-out, temporal-held-out, and separate attention-bias/quantizer/regularizer/observer ablations.
- [ ] Verify RED status.
- [ ] Implement adapters rather than duplicating existing LLM owners.
- [ ] Represent the external E8 `head_scales=0` experiment as attention-bias-only ablation, not full E8 ablation.
- [ ] Preserve all physical/phenomenal/nonlocal boundaries.
- [ ] Re-check status and commit.

### Task 7: Rollup, source atlas, and PR status

**Files:**
- Create: `DASHI/Cognition/Teleodynamics/Everything.agda`
- Modify: `DASHI/Cognition/TeleodynamicsEverything.agda`
- Modify: `DASHI/Cognition/TeleodynamicsSourceAtlas.agda`
- Modify: PR #1093 body.

**Interfaces:**
- Consumes: Tasks 1–6.
- Produces: one import surface and provenance ledger for all newly implemented claims.

- [ ] Add rollup imports and regression imports.
- [ ] Extend source atlas with external engineering-source vs DASHI-derived vs open-promotion entries.
- [ ] Fetch exact-head workflow runs/status and report only observed verification state.
- [ ] Update PR body with implemented owners, exact remaining mathematical walls, and verification boundary.
- [ ] Commit.

### Task 8: Lean mirror of the genuinely generic mathematics

**Files:**
- Create: `Integration/TeleodynamicsLila.lean`
- Create: `Integration/TeleodynamicsExceptionalPrior.lean`
- Modify: `Integration/TeleodynamicsRegression.lean`
- Modify: `Integration/Teleodynamics.lean`

**Interfaces:**
- Consumes: existing Lean teleodynamics branch and Mathlib.
- Produces: orthogonal shared-Q/K cancellation in an inner-product/matrix-friendly finite setting, rank-one bias zero-scale reduction, generic codebook/prior records, and exceptional prior configuration data.

- [ ] Write Lean regression examples first on PR #42 branch.
- [ ] Verify RED via exact-head workflow/build status.
- [ ] Implement minimal generic theorems; do not mirror Agda-only provenance scaffolding unless it closes a Lean consumer.
- [ ] Run/fetch exact-head workflow status and update PR #42 body accordingly.
- [ ] Commit.

## Completion Boundary

The implementation is complete at source level when Tasks 1–8 are written and both rollups import their new surfaces. It is machine-checked only where exact-head Agda/Lean runs are observed green. Any unavailable compiler or absent workflow remains explicitly `KERNEL-UNVERIFIED`; it must not be described as passing by inference.
