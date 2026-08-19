module DASHI.Cognition.PNF.OptimizationEconomyExact where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import DASHI.Cognition.PNF.ComplexityArithmetic
  using (_+ᶜ_; _*ᶜ_; _≤ᶜ_; ≤ᶜ-refl)

------------------------------------------------------------------------
-- Cheapest equivalent representation.
--
-- Once semantic admissibility is fixed, physical optimisation asks whether an
-- equivalent consumer observation can be computed from a smaller/bounded source
-- carrier.  In particular, an accumulated historical relation must not be
-- treated as authority for a projection when the finite changed fibre already
-- determines the same result.
------------------------------------------------------------------------

record DeltaProjectionExact
  (History Delta Projection : Set)
  : Set₁ where
  field
    projectHistory : History → Projection
    projectDelta : Delta → Projection
    deltaOf : History → Delta
    deltaProjectionExact : ∀ history →
      projectDelta (deltaOf history) ≡ projectHistory history

open DeltaProjectionExact public

deltaProjectionMayReplaceHistoryProjection :
  ∀ {History Delta Projection : Set}
    (law : DeltaProjectionExact History Delta Projection)
    (history : History) →
  projectDelta law (deltaOf law history) ≡ projectHistory law history
deltaProjectionMayReplaceHistoryProjection law history =
  deltaProjectionExact law history

------------------------------------------------------------------------
-- Parent-interface closure from bounded child fibres.
------------------------------------------------------------------------

record ChildFibreClosureExact
  (AccumulatedLookup ChildFibre ParentLookup : Set)
  : Set₁ where
  field
    closeFromAccumulated : AccumulatedLookup → ParentLookup
    childFibre : AccumulatedLookup → ChildFibre
    closeFromChildren : ChildFibre → ParentLookup
    childClosureExact : ∀ accumulated →
      closeFromChildren (childFibre accumulated)
      ≡ closeFromAccumulated accumulated

open ChildFibreClosureExact public

boundedChildFibrePreservesParentLookup :
  ∀ {AccumulatedLookup ChildFibre ParentLookup : Set}
    (law : ChildFibreClosureExact AccumulatedLookup ChildFibre ParentLookup)
    (accumulated : AccumulatedLookup) →
  closeFromChildren law (childFibre law accumulated)
  ≡ closeFromAccumulated law accumulated
boundedChildFibrePreservesParentLookup law accumulated =
  childClosureExact law accumulated

------------------------------------------------------------------------
-- Physical amplification receipts.
--
-- Ratios are empirical runtime observations, but their admissible bounds can be
-- stated exactly without floating point.  A multiplier k bounds history-read
-- amplification when historyRowsExamined ≤ k * touchedSemanticRows, and bounds
-- write amplification analogously.
------------------------------------------------------------------------

record AmplificationReceipt : Set where
  field
    touchedSemanticRows : Nat
    historyRowsExamined : Nat
    attemptedWrites : Nat
    semanticallyNewWrites : Nat

open AmplificationReceipt public

record AmplificationBound
  (receipt : AmplificationReceipt)
  (historyMultiplier writeMultiplier : Nat)
  : Set where
  field
    historyBound :
      historyRowsExamined receipt
      ≤ᶜ (historyMultiplier *ᶜ touchedSemanticRows receipt)
    writeBound :
      attemptedWrites receipt
      ≤ᶜ (writeMultiplier *ᶜ semanticallyNewWrites receipt)

------------------------------------------------------------------------
-- Runtime and implementation/change economy are orthogonal vectors.
------------------------------------------------------------------------

record RuntimeEconomy : Set where
  field
    wallTicks : Nat
    semanticWorkUnits : Nat
    peakMemoryUnits : Nat
    ioUnits : Nat
    historyRowsExaminedCost : Nat
    attemptedWritesCost : Nat
    newWorkUnits : Nat
    reusedWorkUnits : Nat

open RuntimeEconomy public

record ArchitectureEconomy : Set where
  field
    newPrimitives : Nat
    newAuthoritySurfaces : Nat
    newExecutionEngines : Nat
    newPersistentSchemas : Nat
    duplicatedCapabilities : Nat
    reusedCapabilities : Nat
    retiredCompatibilitySurfaces : Nat

open ArchitectureEconomy public

------------------------------------------------------------------------
-- Review-oriented novelty burden.
------------------------------------------------------------------------

record NoveltyWeights : Set where
  field
    primitiveWeight : Nat
    authorityWeight : Nat
    engineWeight : Nat
    schemaWeight : Nat
    duplicateWeight : Nat

open NoveltyWeights public

noveltyBurden : NoveltyWeights → ArchitectureEconomy → Nat
noveltyBurden weights architecture =
  (primitiveWeight weights *ᶜ newPrimitives architecture)
  +ᶜ ((authorityWeight weights *ᶜ newAuthoritySurfaces architecture)
  +ᶜ ((engineWeight weights *ᶜ newExecutionEngines architecture)
  +ᶜ ((schemaWeight weights *ᶜ newPersistentSchemas architecture)
  +ᶜ (duplicateWeight weights *ᶜ duplicatedCapabilities architecture))))

------------------------------------------------------------------------
-- Pareto improvement.
--
-- Runtime/architecture cost coordinates may only decrease.  Retirement of a
-- compatibility surface is a benefit coordinate, so it may only increase.
-- StrictImprovement witnesses that at least one coordinate improved strictly;
-- a pure equality is not promoted to an optimisation claim.
------------------------------------------------------------------------

record NonWorseningEconomy
  (beforeRuntime afterRuntime : RuntimeEconomy)
  (beforeArchitecture afterArchitecture : ArchitectureEconomy)
  : Set where
  field
    wallNonWorse : wallTicks afterRuntime ≤ᶜ wallTicks beforeRuntime
    workNonWorse : semanticWorkUnits afterRuntime ≤ᶜ semanticWorkUnits beforeRuntime
    memoryNonWorse : peakMemoryUnits afterRuntime ≤ᶜ peakMemoryUnits beforeRuntime
    ioNonWorse : ioUnits afterRuntime ≤ᶜ ioUnits beforeRuntime
    historyReadNonWorse :
      historyRowsExaminedCost afterRuntime
      ≤ᶜ historyRowsExaminedCost beforeRuntime
    writesNonWorse :
      attemptedWritesCost afterRuntime
      ≤ᶜ attemptedWritesCost beforeRuntime
    newWorkNonWorse : newWorkUnits afterRuntime ≤ᶜ newWorkUnits beforeRuntime
    primitivesNonWorse :
      newPrimitives afterArchitecture ≤ᶜ newPrimitives beforeArchitecture
    authoritiesNonWorse :
      newAuthoritySurfaces afterArchitecture
      ≤ᶜ newAuthoritySurfaces beforeArchitecture
    enginesNonWorse :
      newExecutionEngines afterArchitecture
      ≤ᶜ newExecutionEngines beforeArchitecture
    schemasNonWorse :
      newPersistentSchemas afterArchitecture
      ≤ᶜ newPersistentSchemas beforeArchitecture
    duplicatesNonWorse :
      duplicatedCapabilities afterArchitecture
      ≤ᶜ duplicatedCapabilities beforeArchitecture
    retirementNonWorse :
      retiredCompatibilitySurfaces beforeArchitecture
      ≤ᶜ retiredCompatibilitySurfaces afterArchitecture

open NonWorseningEconomy public

data StrictImprovement
  (beforeRuntime afterRuntime : RuntimeEconomy)
  (beforeArchitecture afterArchitecture : ArchitectureEconomy)
  : Set where
  faster :
    suc (wallTicks afterRuntime) ≤ᶜ wallTicks beforeRuntime →
    StrictImprovement beforeRuntime afterRuntime beforeArchitecture afterArchitecture
  lessWork :
    suc (semanticWorkUnits afterRuntime) ≤ᶜ semanticWorkUnits beforeRuntime →
    StrictImprovement beforeRuntime afterRuntime beforeArchitecture afterArchitecture
  lessHistoryRead :
    suc (historyRowsExaminedCost afterRuntime)
      ≤ᶜ historyRowsExaminedCost beforeRuntime →
    StrictImprovement beforeRuntime afterRuntime beforeArchitecture afterArchitecture
  fewerWrites :
    suc (attemptedWritesCost afterRuntime) ≤ᶜ attemptedWritesCost beforeRuntime →
    StrictImprovement beforeRuntime afterRuntime beforeArchitecture afterArchitecture
  fewerAuthorities :
    suc (newAuthoritySurfaces afterArchitecture)
      ≤ᶜ newAuthoritySurfaces beforeArchitecture →
    StrictImprovement beforeRuntime afterRuntime beforeArchitecture afterArchitecture
  fewerEngines :
    suc (newExecutionEngines afterArchitecture)
      ≤ᶜ newExecutionEngines beforeArchitecture →
    StrictImprovement beforeRuntime afterRuntime beforeArchitecture afterArchitecture
  fewerDuplicates :
    suc (duplicatedCapabilities afterArchitecture)
      ≤ᶜ duplicatedCapabilities beforeArchitecture →
    StrictImprovement beforeRuntime afterRuntime beforeArchitecture afterArchitecture
  moreRetired :
    suc (retiredCompatibilitySurfaces beforeArchitecture)
      ≤ᶜ retiredCompatibilitySurfaces afterArchitecture →
    StrictImprovement beforeRuntime afterRuntime beforeArchitecture afterArchitecture

record ParetoImprovement
  (beforeRuntime afterRuntime : RuntimeEconomy)
  (beforeArchitecture afterArchitecture : ArchitectureEconomy)
  : Set where
  field
    nonWorsening :
      NonWorseningEconomy
        beforeRuntime afterRuntime beforeArchitecture afterArchitecture
    strict :
      StrictImprovement
        beforeRuntime afterRuntime beforeArchitecture afterArchitecture

open ParetoImprovement public

------------------------------------------------------------------------
-- Semantic parity is a prerequisite, not a performance coordinate.
------------------------------------------------------------------------

record SemanticallyComparableOptimization
  (Source Observation : Set)
  : Set₁ where
  field
    beforeObservation : Source → Observation
    afterObservation : Source → Observation
    semanticParity : ∀ source →
      afterObservation source ≡ beforeObservation source

open SemanticallyComparableOptimization public

optimizationCannotBuySpeedWithSemanticDrift :
  ∀ {Source Observation : Set}
    (law : SemanticallyComparableOptimization Source Observation)
    (source : Source) →
  afterObservation law source ≡ beforeObservation law source
optimizationCannotBuySpeedWithSemanticDrift law source = semanticParity law source

------------------------------------------------------------------------
-- Composition-first maturity signal.
--
-- This is deliberately not an LOC theorem.  It expresses the architectural
-- preference that genuinely new primitives should be bounded by already reused
-- generic capabilities for a mature recombinational feature.
------------------------------------------------------------------------

record CompositionDominated
  (architecture : ArchitectureEconomy)
  : Set where
  field
    noveltyBoundedByReuse :
      newPrimitives architecture ≤ᶜ reusedCapabilities architecture

open CompositionDominated public

zeroNoveltyIsCompositionDominated :
  ∀ architecture →
  newPrimitives architecture ≡ zero →
  CompositionDominated architecture
zeroNoveltyIsCompositionDominated architecture proof
  rewrite proof = record { noveltyBoundedByReuse =
    let open DASHI.Cognition.PNF.ComplexityArithmetic in z≤n }
