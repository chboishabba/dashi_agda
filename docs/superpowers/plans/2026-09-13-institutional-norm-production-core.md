# Institutional Norm Production Core Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Implement the first Pareto tranche beneath the approved institutional-norm-production design: naturalisation/provenance loss, fragmentation duality, and situated reasonableness, using existing query-indexed factorisation and observer-refinement machinery.

**Architecture:** Add three focused generic Core owners and one narrow regression root. Each owner proves only finite structural non-factorability/refinement results and non-promotion boundaries. No historical case, neurodivergence diagnosis, legal holding, lobbying-causation claim, or moral-responsibility assignment is encoded in this tranche.

**Tech Stack:** Agda; existing `DASHI.Core.QueryIndexedProjectionAdequacyExact`, `DASHI.Core.ObserverRefinementLatticeExact`, `DASHI.Core.IntersectionalNonFactorability`, `DASHI.Core.Prelude`; GitHub focused workflow/static source checks where execution is available.

**Spec:** `docs/superpowers/specs/2026-09-13-institutional-norm-production-fragmentation-design.md`

## Global Constraints

- Follow parent PR #911; do not duplicate its expert-evidence production files.
- Reuse query-indexed adequacy and observer refinement; no parallel factorisation calculus.
- Citation/source identity imports neither proof nor authority.
- Structural cross-pollination never establishes historical equivalence.
- Proximity/access never promotes to influence, quid pro quo, or causation.
- Trauma/reporting witness is a finite insufficiency witness only: fragmentation neither proves trauma nor falsity.
- Distributed-action witness does not assign historical culpability or equate domains.
- Reasonableness remains indexed; observer dependence does not imply arbitrariness-by-definition.
- No Agda/kernel GREEN claim without an exact-head execution receipt.

---

### Task 1: Institutional norm production / naturalisation

**Files:**
- Create first: `DASHI/Core/InstitutionalNormProductionRegression.agda`
- Create after RED: `DASHI/Core/InstitutionalNormProductionExact.agda`

**Interfaces:**
- Consumes: `Query.QuerySemantics`, `Query.AdequateFor`, `Query.QueryAdequacyDefect`, `Observer.pairObserver`, `Observer.strictPairRefinement`.
- Produces: `BaselineWorld`, `baselineSurface`, `productionHistoryAnswer`, `ProductionHistoryQueryAdequacyDefect`, `productionHistoryNotAdequate`, `baselineWithHistory`, `baselineWithHistoryStrictlyRefinesBaseline`, and `canonicalInstitutionalNormProductionBoundary`.

- [ ] **Step 1: Write the failing regression**

Create `InstitutionalNormProductionRegression.agda` requiring these exact surfaces:

```agda
module DASHI.Core.InstitutionalNormProductionRegression where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)

import DASHI.Core.InstitutionalNormProductionExact as Norm

production-history-erasure-is-a-real-defect :
  Norm.ProductionHistoryQueryAdequacyDefect
production-history-erasure-is-a-real-defect =
  Norm.productionHistoryQueryAdequacyDefect

bare-baseline-cannot-answer-production-history :
  Norm.ProductionHistoryQueryAdequate → ⊥
bare-baseline-cannot-answer-production-history =
  Norm.productionHistoryNotAdequate

retained-history-strictly-refines-baseline :
  Norm.BaselineWithHistoryStrictRefinement
retained-history-strictly-refines-baseline =
  Norm.baselineWithHistoryStrictlyRefinesBaseline

legal-validity-does-not-create-neutrality :
  Norm.legalValidityAutomaticallyPoliticalNeutrality
    Norm.canonicalInstitutionalNormProductionBoundary ≡ false
legal-validity-does-not-create-neutrality = refl

proximity-does-not-create-causation :
  Norm.proximityAutomaticallyEstablishesInfluenceCausation
    Norm.canonicalInstitutionalNormProductionBoundary ≡ false
proximity-does-not-create-causation = refl

formal-equality-does-not-pay-equal-norm-power :
  Norm.formalEqualityAutomaticallyEqualNormProductionPower
    Norm.canonicalInstitutionalNormProductionBoundary ≡ false
formal-equality-does-not-pay-equal-norm-power = refl
```

- [ ] **Step 2: Verify RED structurally**

Check the exact branch path for `DASHI/Core/InstitutionalNormProductionExact.agda` and record that it is absent before implementation. If an Agda runner is available, run:

```bash
agda -i . DASHI/Core/InstitutionalNormProductionRegression.agda
```

Expected: failure because `InstitutionalNormProductionExact` is missing. If execution is unavailable, record only structural RED; do not call it compiler RED.

- [ ] **Step 3: Implement the minimal finite owner**

Use two worlds with the same baseline but different production histories:

```agda
data BaselineWorld : Set where
  negotiatedHistoryWorld : BaselineWorld
  excludedHistoryWorld : BaselineWorld

data BaselineSurface : Set where
  sameInstitutionalBaseline : BaselineSurface

data ProductionHistory : Set where
  negotiatedProductionHistory : ProductionHistory
  excludedProductionHistory : ProductionHistory

data NormQuery : Set where
  baselineIdentityQuery : NormQuery
  productionHistoryQuery : NormQuery

data NormAnswer : Set where
  sameBaselineAnswer : NormAnswer
  negotiatedHistoryAnswer : NormAnswer
  excludedHistoryAnswer : NormAnswer

baselineSurface : BaselineWorld → BaselineSurface
baselineSurface world = sameInstitutionalBaseline

productionHistory : BaselineWorld → ProductionHistory
productionHistory negotiatedHistoryWorld = negotiatedProductionHistory
productionHistory excludedHistoryWorld = excludedProductionHistory

normAnswer : NormQuery → BaselineWorld → NormAnswer
normAnswer baselineIdentityQuery world = sameBaselineAnswer
normAnswer productionHistoryQuery negotiatedHistoryWorld = negotiatedHistoryAnswer
normAnswer productionHistoryQuery excludedHistoryWorld = excludedHistoryAnswer
```

Construct the query defect through `Query.queryAdequacyDefect`, block factorisation, then define `baselineWithHistory = Observer.pairObserver baselineSurface productionHistory` and prove strict refinement with `Observer.strictPairRefinement ... refl (λ ())`.

Add only this boundary record:

```agda
record InstitutionalNormProductionBoundary : Set where
  constructor institutionalNormProductionBoundary
  field
    legalValidityAutomaticallyPoliticalNeutrality : Bool
    legalValidityAutomaticallyMoralJustification : Bool
    formalEqualityAutomaticallyEqualNormProductionPower : Bool
    institutionalFamiliarityAutomaticallyEpistemicSuperiority : Bool
    statusSignalAutomaticallySubstantiveAdequacy : Bool
    lawfulLobbyingAutomaticallyNeutralPolicyOutcome : Bool
    consultationAutomaticallyBalancedParticipation : Bool
    proximityAutomaticallyEstablishesInfluenceCausation : Bool
    naturalisationCanEraseProductionHistory : Bool
    retainedHistoryCanRepairBaselineObserver : Bool
```

Canonical values: first eight `false`, final two `true`.

- [ ] **Step 4: Verify GREEN if executable**

Run the focused regression and owner. Expected both pass. Otherwise inspect exact branch text and retain compile status as unpaid.

- [ ] **Step 5: Commit Task 1**

Commit regression first, then owner as separate commits if possible, preserving the RED/GREEN ordering.

---

### Task 2: Fragmentation composition duality

**Files:**
- Create first: `DASHI/Core/FragmentationCompositionRegression.agda`
- Create after RED: `DASHI/Core/FragmentationCompositionExact.agda`

**Interfaces:**
- Consumes: query-indexed projection adequacy only.
- Produces two independent finite witnesses: reporting-surface insufficiency for event-truth query; local-action intelligibility insufficiency for global-outcome query.

- [ ] **Step 1: Write the failing regression**

Require:

```agda
module DASHI.Core.FragmentationCompositionRegression where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)

import DASHI.Core.FragmentationCompositionExact as Frag

narrative-coherence-cannot-answer-event-truth :
  Frag.EventTruthQueryAdequate → ⊥
narrative-coherence-cannot-answer-event-truth =
  Frag.eventTruthNotAdequate

local-intelligibility-cannot-answer-global-defensibility :
  Frag.GlobalDefensibilityQueryAdequate → ⊥
local-intelligibility-cannot-answer-global-defensibility =
  Frag.globalDefensibilityNotAdequate

fragmentation-does-not-prove-trauma :
  Frag.fragmentedNarrativeAutomaticallyEstablishesTrauma
    Frag.canonicalFragmentationBoundary ≡ false
fragmentation-does-not-prove-trauma = refl

local-role-compliance-does-not-pay-global-justification :
  Frag.localRoleComplianceAutomaticallyGlobalJustification
    Frag.canonicalFragmentationBoundary ≡ false
local-role-compliance-does-not-pay-global-justification = refl
```

- [ ] **Step 2: Verify RED structurally**

Confirm production owner absent before writing it; if Agda available, observe missing-module failure.

- [ ] **Step 3: Implement two minimal independent witnesses**

Reporting specimen:

```agda
data ReportingWorld : Set where
  trueFragmentedWorld falseFragmentedWorld : ReportingWorld

data NarrativeSurface : Set where fragmentedNarrative : NarrativeSurface

data EventTruthAnswer : Set where eventOccurred eventDidNotOccur : EventTruthAnswer

narrativeSurface : ReportingWorld → NarrativeSurface
narrativeSurface world = fragmentedNarrative

eventTruthAnswer : ReportingWorld → EventTruthAnswer
eventTruthAnswer trueFragmentedWorld = eventOccurred
eventTruthAnswer falseFragmentedWorld = eventDidNotOccur
```

Use a one-query `QuerySemantics` and exact collision to show event truth cannot factor through narrative coherence alone.

Distributed-action specimen:

```agda
data DistributedWorld : Set where
  benignComposition harmfulComposition : DistributedWorld

data LocalActionSurface : Set where sameLocallyIntelligibleActions : LocalActionSurface

data GlobalOutcomeAnswer : Set where globallyDefensible globallyIndefensible : GlobalOutcomeAnswer
```

Both worlds project to `sameLocallyIntelligibleActions`, but global answer differs.

Boundary fields:

```text
fragmentedNarrativeAutomaticallyEstablishesTrauma = false
fragmentedNarrativeAutomaticallyEstablishesFalsity = false
coherentNarrativeAutomaticallyEstablishesTruth = false
localRoleComplianceAutomaticallyGlobalJustification = false
routineTaskAutomaticallyHarmless = false
smallContributionAutomaticallyZeroContribution = false
distributedCausationAutomaticallyNoCausation = false
sameStructuralMechanismAutomaticallySameHistoricalEvent = false
localSurfaceCanEraseGlobalAnswer = true
```

- [ ] **Step 4: Verify GREEN if executable**

Run the focused regression and owner; otherwise retain compilation as unpaid.

- [ ] **Step 5: Commit Task 2**

Keep regression-before-owner provenance.

---

### Task 3: Situated observer / reasonableness

**Files:**
- Create first: `DASHI/Core/ObserverSituatedReasonablenessRegression.agda`
- Create after RED: `DASHI/Core/ObserverSituatedReasonablenessExact.agda`

**Interfaces:**
- Consumes: observer refinement and query-indexed adequacy.
- Produces a small observer-index record, explicit empirical/institutional/legal reasonableness separation, and finite observer-expectation collision.

- [ ] **Step 1: Write the failing regression**

Require:

```agda
module DASHI.Core.ObserverSituatedReasonablenessRegression where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)

import DASHI.Core.ObserverSituatedReasonablenessExact as Reason

social-conformity-cannot-answer-reasonableness :
  Reason.ReasonablenessQueryAdequate → ⊥
social-conformity-cannot-answer-reasonableness =
  Reason.reasonablenessNotAdequate

observed-frequency-does-not-create-reasonableness :
  Reason.observedFrequencyAutomaticallyReasonable
    Reason.canonicalSituatedReasonablenessBoundary ≡ false
observed-frequency-does-not-create-reasonableness = refl

institutional-convention-does-not-create-reasonableness :
  Reason.institutionalConventionAutomaticallyReasonable
    Reason.canonicalSituatedReasonablenessBoundary ≡ false
institutional-convention-does-not-create-reasonableness = refl

observer-dependence-is-not-contentlessness :
  Reason.observerDependenceAutomaticallyContentless
    Reason.canonicalSituatedReasonablenessBoundary ≡ false
observer-dependence-is-not-contentlessness = refl
```

- [ ] **Step 2: Verify RED structurally**

Confirm owner absent; observe missing-module failure if executable.

- [ ] **Step 3: Implement the minimal situated reasonableness owner**

Define the index record:

```agda
record ReasonablenessIndex : Set where
  constructor reasonablenessIndex
  field
    institutionReference : String
    sourceContextReference : String
    referencePerspective : String
    relevantFactorSetReference : String
    thresholdReference : String
    consequenceQueryReference : String
    reviewStandardReference : String
```

Keep three separate carrier constructors/types for empirical normality, institutional normality, and legal reasonableness.

Finite witness:

```agda
data ReasonWorld : Set where
  conventionallyPresentedWorld atypicallyPresentedWorld : ReasonWorld

data SocialConformitySurface : Set where
  sameObservedConformity : SocialConformitySurface

data ReasonAnswer : Set where
  withinDeclaredReasonableRange outsideDeclaredReasonableRange : ReasonAnswer
```

Both worlds share the same deliberately coarse social-conformity observation but differ on the declared reasonableness answer after an extra situated coordinate is retained. Use query-indexed adequacy to block recovery from the coarse surface and observer refinement to show the joined surface is strictly finer.

Do **not** name the worlds autistic/neurotypical or traumatised/non-traumatised in the generic owner.

Boundary fields:

```text
observedFrequencyAutomaticallyReasonable = false
institutionalConventionAutomaticallyReasonable = false
socialNormConformityAutomaticallyCredible = false
atypicalAffectAutomaticallyDishonest = false
literalResponseAutomaticallyNonCooperative = false
dysregulationAutomaticallyDangerous = false
narrativeFragmentationAutomaticallyFalse = false
observerDependenceAutomaticallyContentless = false
reasonablenessRequiresDeclaredIndex = true
joinedObserverCanRetainSituatedCoordinate = true
```

- [ ] **Step 4: Verify GREEN if executable**

Run owner/regression if possible; otherwise retain kernel status unpaid.

- [ ] **Step 5: Commit Task 3**

Keep regression-before-owner ordering.

---

### Task 4: Narrow roll-up and focused certification surface

**Files:**
- Create: `DASHI/Core/InstitutionalNormProductionEverything.agda`
- Create: `.github/workflows/institutional-norm-production-core.yml`

**Interfaces:**
- Consumes all three owners/regressions.
- Produces one opt-in aggregate and one focused exact-head certification path.

- [ ] **Step 1: Add a roll-up file that imports only the six new Core files**

```agda
module DASHI.Core.InstitutionalNormProductionEverything where

import DASHI.Core.InstitutionalNormProductionExact
import DASHI.Core.InstitutionalNormProductionRegression
import DASHI.Core.FragmentationCompositionExact
import DASHI.Core.FragmentationCompositionRegression
import DASHI.Core.ObserverSituatedReasonablenessExact
import DASHI.Core.ObserverSituatedReasonablenessRegression
```

- [ ] **Step 2: Add focused workflow**

Use the repo's current focused Agda pattern. Path-filter only the new tranche plus its direct generic dependencies. Kernel-check the three regressions and aggregate. Include a narrow trust-escape scan for `postulate`, unsolved metas and explicit compiler escapes in the new owner/regression files.

- [ ] **Step 3: Inspect workflow run state for exact head**

If GitHub schedules a PR/push run, record its exact conclusion and artifact/log. If no run exists, state `certification unpaid`; never infer success from workflow presence.

- [ ] **Step 4: Commit Task 4**

Commit roll-up and workflow.

---

## Plan self-review

- Spec coverage for this plan: paid only for the first three generic owners plus focused certification; legal-reasonableness, operational-legality, responsibility, expert adapter, historical fixtures and consequence-severity remain intentionally deferred to later plans.
- No historical equivalence or diagnosis is encoded in generic finite witness names.
- `QueryIndexedProjectionAdequacyExact` remains the single factorisation interface.
- `ObserverRefinementLatticeExact` remains the single refinement interface.
- Lobbying/proximity appears only as a no-promotion boundary in this core tranche; source-bearing concrete proximity edges remain owned by existing/future attributed fixtures.
- Compilation status remains separate from source presence and structural inspection.
