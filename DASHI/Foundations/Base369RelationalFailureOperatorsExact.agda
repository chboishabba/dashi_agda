module DASHI.Foundations.Base369RelationalFailureOperatorsExact where

------------------------------------------------------------------------
-- DASHI CONTRIBUTION
--
-- Projection loss, prior contamination and recursive boundary expansion are
-- independent failures.  Defensive reflection is separated from genuine
-- inversion, and behaviour is separated from consent by counterfactual refusal
-- and capacity witnesses.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; suc)

record ProjectionLoss : Set₁ where
  constructor projectionLoss
  field
    Latent Observable : Set
    project : Latent → Observable
    distinctLatentA distinctLatentB : Latent
    sameObservation : project distinctLatentA ≡ project distinctLatentB

open ProjectionLoss public

record PriorContamination : Set₁ where
  constructor priorContamination
  field
    Current PriorTemplate Perceived : Set
    observeCurrent : Current → Perceived
    contaminate : Current → PriorTemplate → Perceived

open PriorContamination public

record UncontaminatedObservation (p : PriorContamination) : Set₁ where
  constructor uncontaminatedObservation
  field
    current : Current p
    prior : PriorTemplate p
    contaminationAbsent : contaminate p current prior ≡ observeCurrent p current

open UncontaminatedObservation public

record BoundaryMeasure : Set where
  constructor boundaryMeasure
  field unresolvedCount : Nat

open BoundaryMeasure public

record ProductiveRefinement : Set₁ where
  constructor productiveRefinement
  field
    before after : BoundaryMeasure
    reductionWitness : Set

record RecursiveBoundaryExpansion : Set₁ where
  constructor recursiveBoundaryExpansion
  field
    initiatingBoundary : Set
    newlySpawnedBoundary : Nat → Set
    originalRemainsOpen : (depth : Nat) → Set
    expansionWitness :
      (depth : Nat) → unresolvedCount (boundaryMeasure (suc depth)) ≡ suc depth

record GroundedComplaint : Set₁ where
  constructor groundedComplaint
  field
    Act Label : Set
    particulars : Act
    classification : Label

open GroundedComplaint public

record GenuineInversion
  (source target : GroundedComplaint) : Set₁ where
  constructor genuineInversion
  field
    inverseAct : Act target
    evidentialTransport : Set

record DefensiveReflection (source : GroundedComplaint) : Set₁ where
  constructor defensiveReflection
  field
    ReturnedLabel : Set
    returnedLabel : ReturnedLabel
    noParticularsTransported : Set
    sourceStillUnresolved : Set

data RepresentationalType : Set where
  presentPreference presentFeeling rememberedEvent attributedIntention
    proposal assent unilateralDecision jointAgreement publicFact :
    RepresentationalType

record PromotionWitness
  (source target : RepresentationalType) : Set₁ where
  constructor promotionWitness
  field evidence : Set

-- No generic coercion between representational types is provided.

data BehaviourObservation : Set where
  performed silent withdrew froze : BehaviourObservation

data LatentChoiceState : Set where
  willing complyingUnderPressure submitted frozenWithoutChoice : LatentChoiceState

observeChoice : LatentChoiceState → BehaviourObservation
observeChoice willing = performed
observeChoice complyingUnderPressure = performed
observeChoice submitted = performed
observeChoice frozenWithoutChoice = froze

performedObservationIsNonInjective :
  observeChoice willing ≡ observeChoice complyingUnderPressure
performedObservationIsNonInjective = refl

record ConsentCounterfactual : Set where
  constructor consentCounterfactual
  field
    refusalAvailable deferralAvailable capacityAvailable : Bool

open ConsentCounterfactual public

record ValidChoiceTransition : Set where
  constructor validChoiceTransition
  field
    latentState : LatentChoiceState
    counterfactual : ConsentCounterfactual
    refusalWasAvailable : refusalAvailable counterfactual ≡ true
    capacityWasAvailable : capacityAvailable counterfactual ≡ true

open ValidChoiceTransition public
