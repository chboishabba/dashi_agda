module DASHI.Core.MechanismModelDiscriminationExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List)
open import Agda.Builtin.String using (String)

import DASHI.Core.AffectedDependencyClosureExact as Dependency
import DASHI.Core.DiscriminatorSynthesisExact as Discriminator
import DASHI.Core.ReopenableHypothesisForestExact as Forest

------------------------------------------------------------------------
-- DOMAIN-NEUTRAL MODEL / MECHANISM DISCRIMINATION
--
-- This abstracts a recurring pattern already present across DASHI: multiple
-- hidden explanatory worlds may collapse to the same coarse observation; a
-- matched discriminating panel can separate some of them; residuals reopen the
-- dependency-reachable carrier rather than invalidating the entire model; and
-- refutation remains stronger than mere tension or staleness.
------------------------------------------------------------------------

data QualitativeDirection : Set where
  stronglyDown down unchanged up stronglyUp unresolvedDirection
  : QualitativeDirection

data ResidualClass : Set where
  consistent
  tension
  discriminating
  falsified
  unresolvedResidual
  : ResidualClass

record ModelHypothesis : Set where
  constructor modelHypothesis
  field
    hypothesisId : String
    familyReference : String
    requiredCarrier : String
    excludedShortcut : String

open ModelHypothesis public

record ObservableCoordinate : Set where
  constructor observableCoordinate
  field
    observableId : String
    measurementReference : String
    observationContext : String

open ObservableCoordinate public

record PredictedObservation : Set where
  constructor predictedObservation
  field
    hypothesis : ModelHypothesis
    observable : ObservableCoordinate
    direction : QualitativeDirection
    predictionBasis : String
    targetContextValidated : Bool

open PredictedObservation public

record ObservedEvidence : Set where
  constructor observedEvidence
  field
    observable : ObservableCoordinate
    direction : QualitativeDirection
    evidenceReference : String
    protocolValidated : Bool

open ObservedEvidence public

record ModelResidual : Set where
  constructor modelResidual
  field
    prediction : PredictedObservation
    observation : ObservedEvidence
    residualClass : ResidualClass
    interpretation : String

open ModelResidual public

record MatchedDiscriminationPanel : Set where
  constructor matchedDiscriminationPanel
  field
    hypotheses : List ModelHypothesis
    observables : List ObservableCoordinate
    predictions : List PredictedObservation
    sameObjectContext : Bool
    sameObjectContextValidated : Bool
    panelReference : String

open MatchedDiscriminationPanel public

------------------------------------------------------------------------
-- Selective reopening.
------------------------------------------------------------------------

record ReopenDirective : Set where
  constructor reopenDirective
  field
    hypothesis : ModelHypothesis
    changedCarrier : String
    targetCarrier : String
    obligationReference : String
    reason : String

open ReopenDirective public

record DependencyScopedReopen : Set₁ where
  constructor dependencyScopedReopen
  field
    Carrier : Set
    Depends : Carrier → Carrier → Set
    changed : Carrier
    target : Carrier
    residual : ModelResidual
    residualIsDiscriminating : residualClass residual ≡ discriminating
    affected : Dependency.AffectedClosure Depends changed target
    reopeningReference : String

open DependencyScopedReopen public

dependencyScopedReopenObligation :
  (reopening : DependencyScopedReopen) →
  Dependency.ReopeningObligation
    (Depends reopening)
    (changed reopening)
    (target reopening)
dependencyScopedReopenObligation reopening =
  Dependency.reopeningObligation (affected reopening)

------------------------------------------------------------------------
-- Hypothesis-status bridge.
--
-- A domain may supply its own proof-bearing refutation and reopening evidence
-- while sharing the generic active/reopenable/refuted transition law.
------------------------------------------------------------------------

record ModelStatusSemantics : Set₁ where
  constructor modelStatusSemantics
  field
    RefutationReceipt : ModelHypothesis → Set
    ReopeningReceipt : Forest.DormancyReason → ModelHypothesis → Set

open ModelStatusSemantics public

asForestSemantics :
  ModelStatusSemantics → Forest.HypothesisSemantics ModelHypothesis
asForestSemantics semantics =
  Forest.hypothesisSemantics
    (RefutationReceipt semantics)
    (ReopeningReceipt semantics)

------------------------------------------------------------------------
-- Discriminator-synthesis bridge.
--
-- The model-discrimination panel is intentionally compatible with the already
-- existing generic experiment-bundle machinery.  A domain can prove that a
-- prospective measurement separates a concrete collision without changing the
-- model-discrimination vocabulary.
------------------------------------------------------------------------

record CollisionDiscriminatorWeld : Set₁ where
  constructor collisionDiscriminatorWeld
  field
    World Existing : Set
    existingObservation : World → Existing
    collision : Discriminator.CurrentObserverCollision existingObservation
    bundle : Discriminator.ExperimentBundle World
    separation :
      Discriminator.BundleSeparates
        bundle
        (Discriminator.left collision)
        (Discriminator.right collision)
    calibrationReference : String

open CollisionDiscriminatorWeld public

------------------------------------------------------------------------
-- Mixed / multi-lane models.
------------------------------------------------------------------------

record MixedModelAdmission : Set where
  constructor mixedModelAdmission
  field
    mixedHypothesis : ModelHypothesis
    componentLaneReference : String
    jointPanelReference : String
    singleLaneInsufficiencyReference : String
    positiveMultiLaneEvidence : Bool

open MixedModelAdmission public

record ModelDiscriminationBoundary : Set where
  constructor modelDiscriminationBoundary
  field
    sameEndpointImpliesSameCause : Bool
    sameEndpointImpliesSameCauseIsFalse :
      sameEndpointImpliesSameCause ≡ false

    oneMatchingCoordinateEstablishesModel : Bool
    oneMatchingCoordinateEstablishesModelIsFalse :
      oneMatchingCoordinateEstablishesModel ≡ false

    oneTensionAutomaticallyRefutesModel : Bool
    oneTensionAutomaticallyRefutesModelIsFalse :
      oneTensionAutomaticallyRefutesModel ≡ false

    staleOrReopenableEqualsRefuted : Bool
    staleOrReopenableEqualsRefutedIsFalse :
      staleOrReopenableEqualsRefuted ≡ false

    discriminatingResidualCanReopenDependencyReachableCarrier : Bool
    discriminatingResidualCanReopenDependencyReachableCarrierIsTrue :
      discriminatingResidualCanReopenDependencyReachableCarrier ≡ true

    mixedModelRequiresPositiveMultiLaneEvidence : Bool
    mixedModelRequiresPositiveMultiLaneEvidenceIsTrue :
      mixedModelRequiresPositiveMultiLaneEvidence ≡ true

    matchedPanelCanBeDesignedToSeparateCollidingWorlds : Bool
    matchedPanelCanBeDesignedToSeparateCollidingWorldsIsTrue :
      matchedPanelCanBeDesignedToSeparateCollidingWorlds ≡ true

canonicalModelDiscriminationBoundary : ModelDiscriminationBoundary
canonicalModelDiscriminationBoundary =
  modelDiscriminationBoundary
    false refl
    false refl
    false refl
    false refl
    true refl
    true refl
    true refl
