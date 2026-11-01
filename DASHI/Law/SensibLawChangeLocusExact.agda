module DASHI.Law.SensibLawChangeLocusExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Law.SensibLawComparativeWorldIRExact as Comparative
import DASHI.Core.WorldRepresentationSeparationExact as World

------------------------------------------------------------------------
-- M11.1 / S26.9 TYPED CHANGE LOCUS
--
-- The green ComparativeDelta carrier says WHAT changed.  ChangeLocus adds
-- WHERE that change occurred without changing the existing comparative ABI.
------------------------------------------------------------------------

data ChangeLayer : Set where
  worldLayer : ChangeLayer
  worldEvidenceLayer : ChangeLayer
  observationLayer : ChangeLayer
  representationLayer : ChangeLayer
  theoryLayer : ChangeLayer
  beliefLayer : ChangeLayer
  consumerProjectionLayer : ChangeLayer
  reviewLayer : ChangeLayer
  scopeLayer : ChangeLayer
  applicabilityLayer : ChangeLayer
  proofOutcomeLayer : ChangeLayer
  residualOutcomeLayer : ChangeLayer

record ChangeLocus : Set where
  constructor change-locus
  field
    locusRef : String
    delta : Comparative.ComparativeDelta
    layer : ChangeLayer
    sublayerRef : String
    candidateOnly : Bool
    candidateOnlyIsTrue : candidateOnly ≡ true
    createsSemanticAuthority : Bool
    createsSemanticAuthorityIsFalse : createsSemanticAuthority ≡ false
    createsClaimTruth : Bool
    createsClaimTruthIsFalse : createsClaimTruth ≡ false

open ChangeLocus public

theoryDeltaFixture : Comparative.ComparativeDelta
theoryDeltaFixture =
  Comparative.comparative-delta
    "delta:gravity:newton-to-relativity"
    Comparative.factChanged
    Comparative.worldInput
    "coordinate:theory:gravity"
    ""
    true
    false
    false

theoryChangeLocus : ChangeLocus
theoryChangeLocus =
  change-locus
    "locus:gravity:theory-revision"
    theoryDeltaFixture
    theoryLayer
    "gravity-theory-representation"
    true refl
    false refl
    false refl

observationDeltaFixture : Comparative.ComparativeDelta
observationDeltaFixture =
  Comparative.comparative-delta
    "delta:gravity:coarse-to-refined-observer"
    Comparative.factChanged
    Comparative.worldInput
    "coordinate:observation:gravity"
    ""
    true
    false
    false

observationChangeLocus : ChangeLocus
observationChangeLocus =
  change-locus
    "locus:gravity:observation-refinement"
    observationDeltaFixture
    observationLayer
    "instrument-resolution"
    true refl
    false refl
    false refl

------------------------------------------------------------------------
-- PR #1028 supplies the formal ancestor for the no-collapse boundary.
------------------------------------------------------------------------

worldRepresentationBoundary : World.WorldRepresentationBoundary
worldRepresentationBoundary = World.canonicalWorldRepresentationBoundary

worldAndTheoryAlreadySeparate :
  World.worldAndTheoryAreSeparateCoordinates worldRepresentationBoundary ≡ true
worldAndTheoryAlreadySeparate = refl

theoryMayChangeWithoutWorldAlready :
  World.theoryMayChangeWithoutWorldChange worldRepresentationBoundary ≡ true
theoryMayChangeWithoutWorldAlready = refl

observationMayEraseWorldDistinctionAlready :
  World.observationMayEraseWorldDistinctions worldRepresentationBoundary ≡ true
observationMayEraseWorldDistinctionAlready = refl

observerRefinementDoesNotChangeWorldAlready :
  World.observerRefinementAutomaticallyChangesWorld worldRepresentationBoundary ≡ false
observerRefinementDoesNotChangeWorldAlready = refl

data TheoryDeltaIsWorldDelta : Set where
data ObservationDeltaIsWorldDelta : Set where
data ProjectionDeltaIsWorldDelta : Set where
data BeliefDeltaIsWorldDelta : Set where
data ProofOutcomeIsInputLayer : Set where
data ResidualOutcomeIsInputLayer : Set where

theoryDeltaDoesNotCollapseToWorld :
  TheoryDeltaIsWorldDelta → ⊥
theoryDeltaDoesNotCollapseToWorld ()

observationDeltaDoesNotCollapseToWorld :
  ObservationDeltaIsWorldDelta → ⊥
observationDeltaDoesNotCollapseToWorld ()

projectionDeltaDoesNotCollapseToWorld :
  ProjectionDeltaIsWorldDelta → ⊥
projectionDeltaDoesNotCollapseToWorld ()

beliefDeltaDoesNotCollapseToWorld :
  BeliefDeltaIsWorldDelta → ⊥
beliefDeltaDoesNotCollapseToWorld ()

proofOutcomeDoesNotBecomeInputLayer :
  ProofOutcomeIsInputLayer → ⊥
proofOutcomeDoesNotBecomeInputLayer ()

residualOutcomeDoesNotBecomeInputLayer :
  ResidualOutcomeIsInputLayer → ⊥
residualOutcomeDoesNotBecomeInputLayer ()

record ChangeLocusBoundary : Set where
  constructor changeLocusBoundary
  field
    deltaKindAndLayerAreSeparateAxes : Bool
    deltaKindAndLayerAreSeparateAxesIsTrue :
      deltaKindAndLayerAreSeparateAxes ≡ true

    theoryDeltaEqualsWorldDelta : Bool
    theoryDeltaEqualsWorldDeltaIsFalse :
      theoryDeltaEqualsWorldDelta ≡ false

    observationDeltaEqualsWorldDelta : Bool
    observationDeltaEqualsWorldDeltaIsFalse :
      observationDeltaEqualsWorldDelta ≡ false

    projectionDeltaEqualsWorldDelta : Bool
    projectionDeltaEqualsWorldDeltaIsFalse :
      projectionDeltaEqualsWorldDelta ≡ false

    outcomeLayerMayServeAsInputCause : Bool
    outcomeLayerMayServeAsInputCauseIsFalse :
      outcomeLayerMayServeAsInputCause ≡ false

    changeLocusCreatesSemanticAuthority : Bool
    changeLocusCreatesSemanticAuthorityIsFalse :
      changeLocusCreatesSemanticAuthority ≡ false

    changeLocusCreatesClaimTruth : Bool
    changeLocusCreatesClaimTruthIsFalse :
      changeLocusCreatesClaimTruth ≡ false

open ChangeLocusBoundary public

canonicalChangeLocusBoundary : ChangeLocusBoundary
canonicalChangeLocusBoundary =
  changeLocusBoundary
    true refl
    false refl
    false refl
    false refl
    false refl
    false refl
    false refl
