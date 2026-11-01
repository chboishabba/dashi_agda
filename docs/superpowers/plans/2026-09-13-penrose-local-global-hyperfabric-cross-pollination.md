# Penrose Local-Global Hyperfabric Cross-Pollination Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Implement one thin Interop owner that makes the approved Penrose ↔ LocalFibre ↔ graph-colouring ↔ NDim local-to-global dependency correspondence executable without identifying any domain objects, theorems, or authorities.

**Architecture:** The new owner consumes existing canonical surfaces only. It defines a small descriptive role vocabulary, domain-specific adapter receipts, the four mandatory WrongType firewalls, and a constructive-gluing versus obstruction/reductio duality. It is stacked directly on PR #908 so the Penrose causal/compactness/authority owners are available without copying them.

**Tech Stack:** Agda; Python structural checker; GitHub branch stacking.

**Spec:** `docs/superpowers/specs/2026-09-13-penrose-local-global-hyperfabric-cross-pollination-design.md`

## Global Constraints

- Keep branch `agent/penrose-local-global-xpollination` stacked directly on `agent/gr-penrose-causal-boundary-v2` / PR #908.
- Do not modify canonical Penrose, LocalFibre, NDim/Pareto, or graph-colouring kernels.
- Reuse existing source receipts; add no new external source claim unless a genuinely new factual claim is introduced.
- Citation/source identity imports neither proof nor authority.
- Cross-pollination is retrospective structural correspondence only; it does not assert historical influence, theorem identity, semantic identity, or shared domain ontology.
- Preserve Penrose same-object identity: the compact and noncompact claims apply to the same `E+(T)` reductio object.
- First tranche excludes RSA, Fly/MaleCNS, SensibLaw, Navier-Stokes, and other downstream consumers.
- CI availability is out of scope; do not claim Agda kernel success without a fresh receipt.

---

### Task 1: RED structural contract

**Files:**
- Create: `scripts/check_penrose_local_global_hyperfabric_cross_pollination.py`
- Expected-absent production target: `DASHI/Interop/PenroseLocalGlobalHyperfabricCrossPollinationExact.agda`

**Interfaces:**
- Consumes: approved spec names.
- Produces: a fail-closed structural contract that requires the exact first-tranche surfaces before production exists.

- [ ] **Step 1: Write the failing structural checker**

Require the production owner and these exact symbols:

```text
LocalGlobalRole
localWitness
boundaryRestriction
compatibilityCondition
globalCompatibleObject
projectionReduction
globalObstruction
reductioConclusion

PenroseLocalGlobalAdapter
canonicalPenroseLocalGlobalAdapter
GraphColouringLocalGlobalAdapter
canonicalGraphColouringLocalGlobalAdapter
LocalFibreLocalGlobalAdapter
canonicalLocalFibreLocalGlobalAdapter
NDimProjectionAdapter
canonicalNDimProjectionAdapter

ConstructiveGluingObstructionDuality
canonicalConstructiveGluingObstructionDuality

localValidityDoesNotImplyGlobalValidity
projectionValidityDoesNotImplySourceSufficiency
boundedLocalCarrierDoesNotImplyGlobalCompactnessOrClosure
sharedProofArchitectureDoesNotIdentifyDomainTheorems
penroseProjectionIsNotParetoAxisProjection
horismosIsNotHyperfabricGlobalSection
graphSeamCompatibilityIsNotLorentzianCompatibility
sameObjectReductioRequiresSameObjectIdentity

crossPollinationAddsNoNewSourceAuthority
crossPollinationIsRetrospectiveNotHistoricalInfluence
```

The checker must also require imports of:

```text
DASHI.Reasoning.LocalFibreHyperfabricExact
DASHI.Core.NDimParetoHyperfabricExact
DASHI.Combinatorics.GraphColouringRecolourPantsSnowballExact
DASHI.Physics.Gravity.PenroseGlobalHorismosContradictionExact
DASHI.Physics.Gravity.PenroseGlobalCausalityAuthorityExact
```

- [ ] **Step 2: Verify RED structurally**

Use the exact branch lookup for `DASHI/Interop/PenroseLocalGlobalHyperfabricCrossPollinationExact.agda` and require it to be absent before production creation. Record the 404/absence as the RED receipt. Do not claim Python execution if it cannot be run in this environment.

- [ ] **Step 3: Commit checker-first RED**

Commit only the checker.

---

### Task 2: Minimal Interop owner

**Files:**
- Create: `DASHI/Interop/PenroseLocalGlobalHyperfabricCrossPollinationExact.agda`

**Interfaces:**
- Consumes:
  - `DASHI.Reasoning.LocalFibreHyperfabricExact.canonicalLocalFibreAuthorityMap`
  - `DASHI.Core.NDimParetoHyperfabricExact.canonicalNDimParetoHyperfabricBoundary`
  - `DASHI.Combinatorics.GraphColouringRecolourPantsSnowballExact.canonicalGraphColouringPantsBoundary`
  - `DASHI.Physics.Gravity.PenroseGlobalHorismosContradictionExact.canonicalPenroseGlobalHorismosBoundary`
  - `DASHI.Physics.Gravity.PenroseGlobalCausalityAuthorityExact.canonicalGlobalCausalityAuthorityReceipt`
- Produces: descriptive role/adapters and exact Bool/equality boundaries only.

- [ ] **Step 1: Define role vocabulary**

Create:

```agda
data LocalGlobalRole : Set where
  localWitness : LocalGlobalRole
  boundaryRestriction : LocalGlobalRole
  compatibilityCondition : LocalGlobalRole
  globalCompatibleObject : LocalGlobalRole
  projectionReduction : LocalGlobalRole
  globalObstruction : LocalGlobalRole
  reductioConclusion : LocalGlobalRole
```

No generic proof calculus, category, or planner is introduced.

- [ ] **Step 2: Add Penrose adapter**

Create `PenroseLocalGlobalAdapter` with descriptive `String` role bindings and exact Bool receipts requiring:

```text
sameHorismosObjectPreserved = true
localFocusingDoesNotAlonePayGlobalObstruction = true
cauchyProjectionIsGlobalCausalityStep = true
sourceAuthorityRemainsOwnedByParent = true
```

The canonical adapter must consume the parent owner fields, especially `sameHorismosObjectCarriesBothReductioClaims` and the Minguzzi authority receipt, rather than restating a new theorem.

- [ ] **Step 3: Add graph-colouring adapter**

Bind existing stages:

```text
localRecolourMove
boundaryRestriction
pantsSeamCompatibility
recursiveGluingCompatibility
globalColouring
```

and preserve `localRecolourImpliesGlobalGluingCompatibility = false` from the canonical graph-colouring boundary.

- [ ] **Step 4: Add LocalFibre adapter**

Bind the existing role map fields:

```text
localStalkOwner
restrictionTransportOwner
globalCompatibilityOwner
```

and explicitly mark that the Penrose global causal object is not identified with a `GlobalSection`.

- [ ] **Step 5: Add NDim projection adapter**

Consume `projectedDominanceImpliesFullDominanceAutomatically = false` from the canonical NDim boundary and record:

```text
fullInformationMayProject = true
projectedResultPromotesSourceSufficiency = false
```

Do not identify Cauchy projection with Pareto axis projection.

- [ ] **Step 6: Add constructive/obstruction duality**

Create `ConstructiveGluingObstructionDuality` with:

```text
constructivePathRecorded = true
obstructionPathRecorded = true
constructiveAndObstructionFormsIdentical = false
sameObjectIdentityRequiredForReductio = true
```

- [ ] **Step 7: Add mandatory WrongType + attribution firewalls**

Expose exact top-level Bool values/equalities for:

```text
localValidityDoesNotImplyGlobalValidity = true
projectionValidityDoesNotImplySourceSufficiency = true
boundedLocalCarrierDoesNotImplyGlobalCompactnessOrClosure = true
sharedProofArchitectureDoesNotIdentifyDomainTheorems = true
penroseProjectionIsNotParetoAxisProjection = true
horismosIsNotHyperfabricGlobalSection = true
graphSeamCompatibilityIsNotLorentzianCompatibility = true
sameObjectReductioRequiresSameObjectIdentity = true
crossPollinationAddsNoNewSourceAuthority = true
crossPollinationIsRetrospectiveNotHistoricalInfluence = true
```

The last two are repo attribution discipline, not external historical claims.

- [ ] **Step 8: Commit minimal production owner**

Commit the owner without changing donor kernels.

---

### Task 3: Focused Agda regression surface

**Files:**
- Create: `DASHI/Interop/PenroseLocalGlobalHyperfabricCrossPollinationRegression.agda`
- Modify: `scripts/check_penrose_local_global_hyperfabric_cross_pollination.py`

**Interfaces:**
- Consumes: top-level firewalls and canonical adapters from Task 2.
- Produces: exact equality proofs pinning the non-promotions and same-object invariant.

- [ ] **Step 1: Extend checker before regression owner**

Require the regression file and exact symbols:

```text
localValidityFirewallRegression
projectionSufficiencyFirewallRegression
boundedLocalCarrierFirewallRegression
sharedArchitectureFirewallRegression
sameObjectIdentityRegression
noNewSourceAuthorityRegression
retrospectiveNotHistoricalRegression
```

- [ ] **Step 2: Verify regression RED structurally**

Confirm the regression owner is absent before creation.

- [ ] **Step 3: Create regression owner**

Each regression is an exact equality to `true`, for example:

```agda
localValidityFirewallRegression :
  Cross.localValidityDoesNotImplyGlobalValidity ≡ true
localValidityFirewallRegression = refl
```

Also pin the Penrose parent same-object receipt through the bridge rather than merely asserting another unrelated Bool.

- [ ] **Step 4: Commit regression tranche**

---

### Task 4: Parent-lineage and snowball metadata

**Files:**
- Modify: `DASHI/Interop/PenroseLocalGlobalHyperfabricCrossPollinationExact.agda`
- Modify: `DASHI/Interop/PenroseLocalGlobalHyperfabricCrossPollinationRegression.agda`

**Interfaces:**
- Consumes: existing source/authority owners only.
- Produces: explicit provenance/snowball discipline for the bridge.

- [ ] **Step 1: Add parent-lineage receipt**

Record descriptive metadata that this bridge consumes the Penrose source/authority chain from the parent branch and does not supersede it. The receipt must distinguish:

```text
parent owner identity
source authority owner identity
cross-pollination owner identity
```

- [ ] **Step 2: Add snowball payment boundary**

Expose:

```text
snowballAcquisitionMayProceedOutOfDependencyOrder = true
snowballPaymentMaySkipUnpaidParentDependency = false
crossDomainAnalogyCreatesSourceAuthority = false
```

This reuses the user's existing snowball discipline without adding sources.

- [ ] **Step 3: Add regression proofs**

Pin those boundaries with exact equality proofs.

- [ ] **Step 4: Commit attribution/snowball refinement**

---

### Task 5: Downstream cross-pollination map without implementation

**Files:**
- Modify: `DASHI/Interop/PenroseLocalGlobalHyperfabricCrossPollinationExact.agda`

**Interfaces:**
- Produces: non-promoting downstream candidate map only; no RSA/Fly/NS/SensibLaw imports.

- [ ] **Step 1: Add candidate-role record**

Create a small descriptive `DownstreamCrossPollinationCandidate` record with fields such as `domain`, `candidateConstructiveRole`, `candidateObstructionRole`, and `implementedInThisTranche : Bool`.

- [ ] **Step 2: Add candidate entries**

Add entries for:

```text
RSA/NDim reducers
Fly/MaleCNS held-out compatible fibres
Navier-Stokes local/global obstruction lanes
SensibLaw evidence/projection authority lanes
```

Every entry must set `implementedInThisTranche = false`.

- [ ] **Step 3: Add global boundary**

Expose `downstreamCandidateMapIsImplementation ≡ false`.

- [ ] **Step 4: Commit candidate-map refinement**

---

### Task 6: Final static review and branch accounting

**Files:**
- No new production files unless review finds a spec mismatch.

**Interfaces:**
- Produces: review receipt only.

- [ ] **Step 1: Re-read spec and diff**

Confirm the final branch changes only:

```text
docs/superpowers/specs/...
docs/superpowers/plans/...
scripts/check_penrose_local_global_hyperfabric_cross_pollination.py
DASHI/Interop/PenroseLocalGlobalHyperfabricCrossPollinationExact.agda
DASHI/Interop/PenroseLocalGlobalHyperfabricCrossPollinationRegression.agda
```

unless an already-existing canonical aggregate is found to be necessary and clearly appropriate.

- [ ] **Step 2: Verify donor kernels unchanged**

Confirm zero diff in:

```text
DASHI/Physics/Gravity/* donor owners
DASHI/Reasoning/LocalFibreHyperfabricExact.agda
DASHI/Core/NDimParetoHyperfabricExact.agda
DASHI/Combinatorics/GraphColouringRecolourPantsSnowballExact.agda
```

- [ ] **Step 3: Verify stack relation**

Compare against `agent/gr-penrose-causal-boundary-v2`; require 0 behind and only the cross-pollination tranche ahead.

- [ ] **Step 4: State certification honestly**

Structural RED receipts from absent files may be reported. Do not claim Python checker execution or Agda kernel GREEN unless freshly executed.
