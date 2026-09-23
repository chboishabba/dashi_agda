module DASHI.Law.SensibLawGravityComparativeWorldExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)

import DASHI.Core.WorldRepresentationSeparationExact as World
import DASHI.Core.IntersectionalNonFactorability as INF
import DASHI.Core.ExperimentalCoordinateDesignExact as Experiment
import DASHI.Core.LawlikeRegularityCounterfactualExact as Regularity
import DASHI.Physics.Laws.EffectiveTheoryLineageExact as Lineage
import DASHI.Law.SensibLawChangeLocusExact as Locus

------------------------------------------------------------------------
-- M11.1 / S26.10-S26.13 GRAVITY COMPARATIVE REGRESSION
--
-- Same represented world, changed theory:
--   coarse query -> same answer
--   discriminating strong-field query -> changed answer
--
-- Same represented world, refined observer:
--   coarse observation may be consumer-sufficient
--   but cannot recover erased world regularity by recharting.
--
-- State change with regularity invariant:
--   changing state does not imply changing regularity/law description.
------------------------------------------------------------------------

data GravityQuery : Set where
  coarseFallQuery : GravityQuery
  strongFieldQuery : GravityQuery

data GravityAnswer : Set where
  fallObserved : GravityAnswer
  newtonStrongFieldAnswer : GravityAnswer
  relativisticStrongFieldAnswer : GravityAnswer

theoryAnswer :
  GravityQuery → World.GravityTheory → GravityAnswer
theoryAnswer coarseFallQuery World.preFormalRegularity = fallObserved
theoryAnswer coarseFallQuery World.newtonianRepresentation = fallObserved
theoryAnswer coarseFallQuery World.relativisticRepresentation = fallObserved
theoryAnswer strongFieldQuery World.preFormalRegularity = newtonStrongFieldAnswer
theoryAnswer strongFieldQuery World.newtonianRepresentation =
  newtonStrongFieldAnswer
theoryAnswer strongFieldQuery World.relativisticRepresentation =
  relativisticStrongFieldAnswer

coarseQueryUnaffectedByTheoryRevision :
  theoryAnswer coarseFallQuery World.newtonianRepresentation
  ≡ theoryAnswer coarseFallQuery World.relativisticRepresentation
coarseQueryUnaffectedByTheoryRevision = refl

strongFieldQueryDistinguishesTheoryRevision :
  theoryAnswer strongFieldQuery World.newtonianRepresentation
  ≡ theoryAnswer strongFieldQuery World.relativisticRepresentation
  → ⊥
strongFieldQueryDistinguishesTheoryRevision ()

sameWorldTheoryRevision :
  World.SameWorldTheoryRevision
sameWorldTheoryRevision = World.newtonToRelativitySameWorldRevision

sameWorldCoordinateHeldFixed :
  World.world sameWorldTheoryRevision ≡ World.highCurvatureFall
sameWorldCoordinateHeldFixed = refl

theoryChangeIsTypedAtTheoryLayer :
  Locus.layer Locus.theoryChangeLocus ≡ Locus.theoryLayer
theoryChangeIsTypedAtTheoryLayer = refl

------------------------------------------------------------------------
-- Observation refinement / non-factorability.
------------------------------------------------------------------------

coarseFallStillCannotExhaustGravityRegularity :
  INF.FactorsThrough
    World.coarseFallObservation
    World.gravityRegularity
  → ⊥
coarseFallStillCannotExhaustGravityRegularity =
  World.coarseFallCannotExhaustGravityRegularity

rechartingStillCannotRecoverErasedGravityReading :
  ∀ {Recharted : Set} →
  (rechart : World.FallObservation → Recharted) →
  INF.FactorsThrough
    (λ state → rechart (World.coarseFallObservation state))
    World.gravityRegularity →
  ⊥
rechartingStillCannotRecoverErasedGravityReading =
  World.rechartingFallObservationStillCannotExhaustGravityRegularity

observationChangeIsTypedAtObservationLayer :
  Locus.layer Locus.observationChangeLocus ≡ Locus.observationLayer
observationChangeIsTypedAtObservationLayer = refl

------------------------------------------------------------------------
-- State change / regularity invariant.
------------------------------------------------------------------------

stateActuallyChangesUnderDeclaredControl :
  Experiment.CoordinateModifiableBy
    Regularity.demoDesign
    Regularity.changingCoordinate
stateActuallyChangesUnderDeclaredControl =
  Regularity.demoStateActuallyChanges

regularityCoordinateRemainsInvariant :
  Experiment.CoordinateInvariantUnder
    Regularity.demoDesign
    Regularity.regularityCoordinate
    Regularity.DeclaredDemoControl
regularityCoordinateRemainsInvariant =
  Regularity.demoRegularityInvariant

------------------------------------------------------------------------
-- Effective-theory lineage: restricted recovery, not replacement.
------------------------------------------------------------------------

newtonGRLineage :
  Lineage.EffectiveTheoryLineage
newtonGRLineage = Lineage.newtonAsRestrictedEffectiveLineage

lineageStatusIsControlledRecovery :
  Lineage.status newtonGRLineage
  ≡ Lineage.controlledEffectiveRecovery
lineageStatusIsControlledRecovery = refl

lineageBoundary : Lineage.EffectiveTheoryLineageBoundary
lineageBoundary = Lineage.canonicalEffectiveTheoryLineageBoundary

olderTheoryCanRemainUseful :
  Lineage.olderTheoryCanRemainUsefulOnRestrictedRegime lineageBoundary ≡ true
olderTheoryCanRemainUseful = refl

newerTheoryDoesNotDeleteOlder :
  Lineage.newerTheoryAutomaticallyDeletesOlderTheory lineageBoundary ≡ false
newerTheoryDoesNotDeleteOlder = refl

effectiveAgreementDoesNotIdentifyWorld :
  Lineage.effectiveAgreementImpliesOntologicalIdentity lineageBoundary ≡ false
effectiveAgreementDoesNotIdentifyWorld = refl

data TheoryRevisionChangesWorldByDefinition : Set where
data ObserverRefinementChangesWorldByDefinition : Set where
data StateChangeChangesRegularityByDefinition : Set where
data NewerTheoryGloballyDeletesOlderTheory : Set where
data EffectiveRecoveryIdentifiesWorldOntology : Set where

theoryRevisionDoesNotChangeWorldByDefinition :
  TheoryRevisionChangesWorldByDefinition → ⊥
theoryRevisionDoesNotChangeWorldByDefinition ()

observerRefinementDoesNotChangeWorldByDefinition :
  ObserverRefinementChangesWorldByDefinition → ⊥
observerRefinementDoesNotChangeWorldByDefinition ()

stateChangeDoesNotChangeRegularityByDefinition :
  StateChangeChangesRegularityByDefinition → ⊥
stateChangeDoesNotChangeRegularityByDefinition ()

newerTheoryDoesNotGloballyDeleteOlderTheory :
  NewerTheoryGloballyDeletesOlderTheory → ⊥
newerTheoryDoesNotGloballyDeleteOlderTheory ()

effectiveRecoveryDoesNotIdentifyWorldOntology :
  EffectiveRecoveryIdentifiesWorldOntology → ⊥
effectiveRecoveryDoesNotIdentifyWorldOntology ()

record GravityComparativeBoundary : Set where
  constructor gravityComparativeBoundary
  field
    sameWorldTheoryChangePossible : Bool
    sameWorldTheoryChangePossibleIsTrue :
      sameWorldTheoryChangePossible ≡ true

    coarseQueryMayRemainUnchanged : Bool
    coarseQueryMayRemainUnchangedIsTrue :
      coarseQueryMayRemainUnchanged ≡ true

    discriminatingQueryMayChange : Bool
    discriminatingQueryMayChangeIsTrue :
      discriminatingQueryMayChange ≡ true

    observationRefinementIsWorldRevision : Bool
    observationRefinementIsWorldRevisionIsFalse :
      observationRefinementIsWorldRevision ≡ false

    stateMayChangeWhileRegularityInvariant : Bool
    stateMayChangeWhileRegularityInvariantIsTrue :
      stateMayChangeWhileRegularityInvariant ≡ true

    effectiveRecoveryIsBooleanReplacement : Bool
    effectiveRecoveryIsBooleanReplacementIsFalse :
      effectiveRecoveryIsBooleanReplacement ≡ false

    comparisonCreatesClaimTruth : Bool
    comparisonCreatesClaimTruthIsFalse :
      comparisonCreatesClaimTruth ≡ false

open GravityComparativeBoundary public

canonicalGravityComparativeBoundary : GravityComparativeBoundary
canonicalGravityComparativeBoundary =
  gravityComparativeBoundary
    true refl
    true refl
    true refl
    false refl
    true refl
    false refl
    false refl
