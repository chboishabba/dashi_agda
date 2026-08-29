module DASHI.Reasoning.DASHIgGrokkingStage67SpecimenExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)

import DASHI.Reasoning.DASHIgGrokkingEmpiricalBridgeExact as Empirical

------------------------------------------------------------------------
-- DASHIg AS A CONCRETE STAGE-6/7 SPECIMEN
--
-- This is deliberately a local finite specimen while PR #636 remains on a
-- sibling branch. It mirrors the prediction-envelope / experiment-
-- discrimination semantics without duplicating those generic owners.
--
-- Current evidence consists only of the pinned preliminary Phase-2 surface.
-- Two future architecture-ordering worlds are intentionally both compatible
-- with that evidence, so the current two-run surface cannot identify a global
-- architecture winner.
------------------------------------------------------------------------

data CurrentPrelimEvidence : Set where
  pinnedTwoRunPhase2Surface : CurrentPrelimEvidence

data FutureWorld : Set where
  geometryVariantWinsHeldOut plainWinsHeldOut : FutureWorld

data FutureArchitectureWinner : Set where
  geometryVariantWinner plainWinner : FutureArchitectureWinner

currentCompatible : CurrentPrelimEvidence → FutureWorld → Set
currentCompatible pinnedTwoRunPhase2Surface geometryVariantWinsHeldOut = ⊤
currentCompatible pinnedTwoRunPhase2Surface plainWinsHeldOut = ⊤

futureWinner : FutureWorld → FutureArchitectureWinner
futureWinner geometryVariantWinsHeldOut = geometryVariantWinner
futureWinner plainWinsHeldOut = plainWinner

currentEvidenceAdmitsGeometryWinningFuture :
  currentCompatible pinnedTwoRunPhase2Surface geometryVariantWinsHeldOut
currentEvidenceAdmitsGeometryWinningFuture = tt

currentEvidenceAdmitsPlainWinningFuture :
  currentCompatible pinnedTwoRunPhase2Surface plainWinsHeldOut
currentEvidenceAdmitsPlainWinningFuture = tt

futureWinnersDiffer :
  futureWinner geometryVariantWinsHeldOut ≡
  futureWinner plainWinsHeldOut → ⊥
futureWinnersDiffer ()

------------------------------------------------------------------------
-- Local point-identifiability definition matching the intended #636 owner.
------------------------------------------------------------------------

PointIdentifiable :
  ∀ {Evidence State Prediction : Set} →
  (Evidence → State → Set) →
  (State → Prediction) →
  Evidence → Set
PointIdentifiable compatible consumer evidence =
  ∀ x y →
    compatible evidence x →
    compatible evidence y →
    consumer x ≡ consumer y

currentPrelimDoesNotIdentifyFutureArchitectureWinner :
  PointIdentifiable currentCompatible futureWinner pinnedTwoRunPhase2Surface → ⊥
currentPrelimDoesNotIdentifyFutureArchitectureWinner identifiable =
  futureWinnersDiffer
    (identifiable
      geometryVariantWinsHeldOut
      plainWinsHeldOut
      tt tt)

------------------------------------------------------------------------
-- A genuinely discriminating held-out measurement can close this tiny envelope.
-- This models the intended Stage-6/7 move: acquire new evidence rather than
-- promote the preliminary table into an architecture theorem.
------------------------------------------------------------------------

data HeldOutMeasurement : Set where
  observedGeometryWinner observedPlainWinner : HeldOutMeasurement

measuresWinner : FutureWorld → HeldOutMeasurement
measuresWinner geometryVariantWinsHeldOut = observedGeometryWinner
measuresWinner plainWinsHeldOut = observedPlainWinner

record RefinedEvidence : Set where
  constructor refinedEvidence
  field
    prior : CurrentPrelimEvidence
    observed : HeldOutMeasurement

refinedCompatible : RefinedEvidence → FutureWorld → Set
refinedCompatible evidence world =
  currentCompatible (prior evidence) world ×
  measuresWinner world ≡ observed evidence

geometryHeldOutEvidence : RefinedEvidence
geometryHeldOutEvidence =
  refinedEvidence pinnedTwoRunPhase2Surface observedGeometryWinner

plainHeldOutEvidence : RefinedEvidence
plainHeldOutEvidence =
  refinedEvidence pinnedTwoRunPhase2Surface observedPlainWinner

geometryMeasurementClosesWinnerEnvelope :
  PointIdentifiable refinedCompatible futureWinner geometryHeldOutEvidence
geometryMeasurementClosesWinnerEnvelope geometryVariantWinsHeldOut geometryVariantWinsHeldOut hx hy = refl
geometryMeasurementClosesWinnerEnvelope geometryVariantWinsHeldOut plainWinsHeldOut hx (_ , ())
geometryMeasurementClosesWinnerEnvelope plainWinsHeldOut geometryVariantWinsHeldOut (_ , ()) hy
geometryMeasurementClosesWinnerEnvelope plainWinsHeldOut plainWinsHeldOut hx hy = refl

plainMeasurementClosesWinnerEnvelope :
  PointIdentifiable refinedCompatible futureWinner plainHeldOutEvidence
plainMeasurementClosesWinnerEnvelope geometryVariantWinsHeldOut geometryVariantWinsHeldOut (_ , ()) hy
plainMeasurementClosesWinnerEnvelope geometryVariantWinsHeldOut plainWinsHeldOut (_ , ()) hy
plainMeasurementClosesWinnerEnvelope plainWinsHeldOut geometryVariantWinsHeldOut hx (_ , ())
plainMeasurementClosesWinnerEnvelope plainWinsHeldOut plainWinsHeldOut hx hy = refl

------------------------------------------------------------------------
-- Tie the specimen back to the pinned empirical source rather than allowing a
-- detached abstract example to masquerade as the experiment itself.
------------------------------------------------------------------------

pinnedProducerCommit : String
pinnedProducerCommit = Empirical.commit Empirical.canonicalDASHIgPhase2Source

prelimRunCountReceipt :
  (Empirical.runCount Empirical.leechDerivativePrelim ≡ 2)
  × (Empirical.runCount Empirical.plainDerivativePrelim ≡ 2)
prelimRunCountReceipt = Empirical.bothDerivativeSummariesAreTwoRunPrelims

------------------------------------------------------------------------
-- Interpretation boundary.
------------------------------------------------------------------------

record DASHIgStage67SpecimenBoundary : Set where
  constructor dashiGStage67SpecimenBoundary
  field
    twoRunPrelimClosesArchitectureDiscrimination : Bool
    twoRunPrelimClosesArchitectureDiscriminationIsFalse :
      twoRunPrelimClosesArchitectureDiscrimination ≡ false

    heldOutDiscriminatingMeasurementCanCloseFiniteEnvelope : Bool
    heldOutDiscriminatingMeasurementCanCloseFiniteEnvelopeIsTrue :
      heldOutDiscriminatingMeasurementCanCloseFiniteEnvelope ≡ true

    finiteSpecimenDuplicatesGenericStage67Owner : Bool
    finiteSpecimenDuplicatesGenericStage67OwnerIsFalse :
      finiteSpecimenDuplicatesGenericStage67Owner ≡ false

    directAdapterShouldReplaceLocalSpecimenAfter636Merge : Bool
    directAdapterShouldReplaceLocalSpecimenAfter636MergeIsTrue :
      directAdapterShouldReplaceLocalSpecimenAfter636Merge ≡ true

canonicalDASHIgStage67SpecimenBoundary : DASHIgStage67SpecimenBoundary
canonicalDASHIgStage67SpecimenBoundary =
  dashiGStage67SpecimenBoundary
    false refl
    true refl
    false refl
    true refl
