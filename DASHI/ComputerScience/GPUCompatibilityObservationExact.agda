module DASHI.ComputerScience.GPUCompatibilityObservationExact where

open import DASHI.Core.Prelude

import DASHI.Core.QueryIndexedProjectionAdequacyExact as Query

------------------------------------------------------------------------
-- QUERY-INDEXED GPU COMPATIBILITY
--
-- Compatibility is not a Boolean attached to a version label.  It is indexed
-- by the consumer question being asked of an observed configuration.  This
-- owner deliberately reuses QueryIndexedProjectionAdequacyExact instead of
-- defining another factorisation calculus.
------------------------------------------------------------------------

data GPUWorld : Set where
  visibleCorrect visibleIncorrect : GPUWorld
  summaryResetSafe summaryResetUnsafe : GPUWorld

data CompatibilityQuery : Set where
  numericalCorrectnessQuery resetSafetyQuery : CompatibilityQuery

compatibilityAnswer : CompatibilityQuery → GPUWorld → Bool
compatibilityAnswer numericalCorrectnessQuery visibleCorrect = true
compatibilityAnswer numericalCorrectnessQuery visibleIncorrect = false
compatibilityAnswer numericalCorrectnessQuery summaryResetSafe = true
compatibilityAnswer numericalCorrectnessQuery summaryResetUnsafe = true
compatibilityAnswer resetSafetyQuery visibleCorrect = true
compatibilityAnswer resetSafetyQuery visibleIncorrect = true
compatibilityAnswer resetSafetyQuery summaryResetSafe = true
compatibilityAnswer resetSafetyQuery summaryResetUnsafe = false

compatibilitySemantics :
  Query.QuerySemantics GPUWorld CompatibilityQuery Bool
compatibilitySemantics = Query.querySemantics compatibilityAnswer

------------------------------------------------------------------------
-- Coarse observers.
------------------------------------------------------------------------

data VisibilityObservation : Set where
  gpuVisible otherVisibility : VisibilityObservation

visibilityProjection : GPUWorld → VisibilityObservation
visibilityProjection visibleCorrect = gpuVisible
visibilityProjection visibleIncorrect = gpuVisible
visibilityProjection summaryResetSafe = otherVisibility
visibilityProjection summaryResetUnsafe = otherVisibility

data SummaryObservation : Set where
  sameSummary otherSummary : SummaryObservation

summaryProjection : GPUWorld → SummaryObservation
summaryProjection visibleCorrect = otherSummary
summaryProjection visibleIncorrect = otherSummary
summaryProjection summaryResetSafe = sameSummary
summaryProjection summaryResetUnsafe = sameSummary

VisibilityCorrectnessDefect : Set₁
VisibilityCorrectnessDefect =
  Query.QueryAdequacyDefect
    visibilityProjection
    compatibilitySemantics
    numericalCorrectnessQuery

visibilityCorrectnessDefect : VisibilityCorrectnessDefect
visibilityCorrectnessDefect =
  Query.queryAdequacyDefect
    visibleCorrect
    visibleIncorrect
    refl
    (λ ())

SummaryResetSafetyDefect : Set₁
SummaryResetSafetyDefect =
  Query.QueryAdequacyDefect
    summaryProjection
    compatibilitySemantics
    resetSafetyQuery

summaryResetSafetyDefect : SummaryResetSafetyDefect
summaryResetSafetyDefect =
  Query.queryAdequacyDefect
    summaryResetSafe
    summaryResetUnsafe
    refl
    (λ ())

------------------------------------------------------------------------
-- Enriched observer: the lost consumer coordinates are carried explicitly.
------------------------------------------------------------------------

record EnrichedCompatibilityObservation : Set where
  constructor enriched-compatibility-observation
  field
    gpuVisibleCoordinate : Bool
    numericalCorrectnessCoordinate : Bool
    resetSafetyCoordinate : Bool
open EnrichedCompatibilityObservation public

enrichedProjection : GPUWorld → EnrichedCompatibilityObservation
enrichedProjection visibleCorrect =
  enriched-compatibility-observation true true true
enrichedProjection visibleIncorrect =
  enriched-compatibility-observation true false true
enrichedProjection summaryResetSafe =
  enriched-compatibility-observation false true true
enrichedProjection summaryResetUnsafe =
  enriched-compatibility-observation false true false

correctnessFromEnriched : EnrichedCompatibilityObservation → Bool
correctnessFromEnriched observation =
  numericalCorrectnessCoordinate observation

resetSafetyFromEnriched : EnrichedCompatibilityObservation → Bool
resetSafetyFromEnriched observation = resetSafetyCoordinate observation

CorrectnessAdequateAfterEnrichment : Set₁
CorrectnessAdequateAfterEnrichment =
  Query.AdequateFor
    enrichedProjection
    compatibilitySemantics
    numericalCorrectnessQuery

correctnessAdequateAfterEnrichment : CorrectnessAdequateAfterEnrichment
correctnessAdequateAfterEnrichment =
  Query.factorsForQuery correctnessFromEnriched (λ
    { visibleCorrect → refl
    ; visibleIncorrect → refl
    ; summaryResetSafe → refl
    ; summaryResetUnsafe → refl
    })

ResetSafetyAdequateAfterEnrichment : Set₁
ResetSafetyAdequateAfterEnrichment =
  Query.AdequateFor
    enrichedProjection
    compatibilitySemantics
    resetSafetyQuery

resetSafetyAdequateAfterEnrichment : ResetSafetyAdequateAfterEnrichment
resetSafetyAdequateAfterEnrichment =
  Query.factorsForQuery resetSafetyFromEnriched (λ
    { visibleCorrect → refl
    ; visibleIncorrect → refl
    ; summaryResetSafe → refl
    ; summaryResetUnsafe → refl
    })

record QueryAdequacyBoundary : Set where
  constructor query-adequacy-boundary
  field
    compatibilityIsIntrinsicVersionBoolean : Bool
    compatibilityRequiresConsumerQuery : Bool
    gpuVisibilityDeterminesNumericalCorrectness : Bool
    summaryProjectionDeterminesResetSafety : Bool
    enrichedObserverCanRepairLostCoordinates : Bool
open QueryAdequacyBoundary public

canonicalQueryAdequacyBoundary : QueryAdequacyBoundary
canonicalQueryAdequacyBoundary =
  query-adequacy-boundary false true false false true

------------------------------------------------------------------------
-- Upgrade compatibility is non-monotone in component recency.
------------------------------------------------------------------------

data UpgradeLane : Set where
  preservedOldABILane fullLatestClassLane : UpgradeLane

laneCompatibility : UpgradeLane → Bool
laneCompatibility preservedOldABILane = true
laneCompatibility fullLatestClassLane = false

record UpgradeCounterexample : Set where
  constructor upgrade-counterexample
  field
    oldLaneCompatible : laneCompatibility preservedOldABILane ≡ true
    newerLaneCompatible : laneCompatibility fullLatestClassLane ≡ false
open UpgradeCounterexample public

canonicalUpgradeCounterexample : UpgradeCounterexample
canonicalUpgradeCounterexample = upgrade-counterexample refl refl

record UpgradeBoundary : Set where
  constructor upgrade-boundary
  field
    newerComponentsPreserveCompatibilityMonotonically : Bool
    compatibilityMustBeRecheckedAfterSeamChange : Bool
    preservedABICanRemainPreferredToLatestClass : Bool
open UpgradeBoundary public

canonicalUpgradeBoundary : UpgradeBoundary
canonicalUpgradeBoundary = upgrade-boundary false true true

------------------------------------------------------------------------
-- Intervention evidence is weaker than mechanism proof.
------------------------------------------------------------------------

record InterventionReceipt : Set where
  constructor intervention-receipt
  field
    outcomeChanged : Bool
    mitigationSucceeded : Bool
    mechanismEstablished : Bool
open InterventionReceipt public

blockingMitigationReceipt : InterventionReceipt
blockingMitigationReceipt = intervention-receipt true true false

record InterventionBoundary : Set where
  constructor intervention-boundary
  field
    successfulMitigationEstablishesRootCause : Bool
    outcomeChangeIsEvidenceForDiscrimination : Bool
    mechanismNeedsIndependentPayment : Bool
open InterventionBoundary public

canonicalInterventionBoundary : InterventionBoundary
canonicalInterventionBoundary = intervention-boundary false true true
