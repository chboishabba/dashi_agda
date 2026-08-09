module DASHI.Foundations.Base369RelationalFailureOperatorsExact where

------------------------------------------------------------------------
-- DASHI CONTRIBUTION
--
-- Three recurrent relational failures are typed separately:
--
--   * projection loss: a rich latent state is replaced by a lossy observable;
--   * prior contamination: the current participant is evaluated through an
--     unresolved identity template;
--   * recursive boundary expansion: each defensive transition spawns a new
--     unresolved object while preserving the original unresolved boundary.
--
-- Defensive reflection is also separated from genuine inversion, and consent
-- is separated from behaviour by the availability of counterfactual refusal.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; suc)

------------------------------------------------------------------------
-- Projection loss.
------------------------------------------------------------------------

record ProjectionLoss : Set₁ where
  constructor projectionLoss
  field
    Latent : Set
    Observable : Set
    project : Latent → Observable
    distinctLatentA : Latent
    distinctLatentB : Latent
    sameObservation : project distinctLatentA ≡ project distinctLatentB

open ProjectionLoss public

-- Equal observed behaviour therefore does not imply equal latent state.

------------------------------------------------------------------------
-- Prior contamination.
------------------------------------------------------------------------

record PriorContamination : Set₁ where
  constructor priorContamination
  field
    Current : Set
    PriorTemplate : Set
    Perceived : Set
    observeCurrent : Current → Perceived
    contaminate : Current → PriorTemplate → Perceived

open PriorContamination public

record UncontaminatedObservation (p : PriorContamination) : Set₁ where
  constructor uncontaminatedObservation
  field
    current : Current p
    prior : PriorTemplate p
    contaminationAbsent :
      contaminate p current prior ≡ observeCurrent p current

open UncontaminatedObservation public

------------------------------------------------------------------------
-- Recursive conflict expansion.
------------------------------------------------------------------------

record BoundaryMeasure : Set where
  constructor boundaryMeasure
  field unresolvedCount : Nat

open BoundaryMeasure public

record ProductiveRefinement : Set where
  constructor productiveRefinement
  field
    before : BoundaryMeasure
    after : BoundaryMeasure
    reductionWitness : Set

record RecursiveBoundaryExpansion : Set where
  constructor recursiveBoundaryExpansion
  field
    initiatingBoundary : Set
    newlySpawnedBoundary : Nat → Set
    originalRemainsOpen : (depth : Nat) → Set
    expansionWitness :
      (depth : Nat) →
      unresolvedCount (boundaryMeasure (suc depth)) ≡ suc depth

------------------------------------------------------------------------
-- Genuine inversion versus defensive role swapping.
------------------------------------------------------------------------

record GroundedComplaint : Set₁ where
  constructor groundedComplaint
  field
    Act : Set
    Label : Set
    particulars : Act
    classification : Label

open GroundedComplaint public

record GenuineInversion
  (source target : GroundedComplaint) : Set₁ where
  constructor genuineInversion
  field
    inverseAct : Act target
    evidentialTransport : Set

record DefensiveReflection
  (source : GroundedComplaint) : Set₁ where
  constructor defensiveReflection
  field
    ReturnedLabel : Set
    returnedLabel : ReturnedLabel
    noParticularsTransported : Set
    sourceStillUnresolved : Set

------------------------------------------------------------------------
-- Typed promotion boundaries.
------------------------------------------------------------------------

data RepresentationalType : Set where
  presentPreference
  presentFeeling
  rememberedEvent
  attributedIntention
  proposal
  assent
  unilateralDecision
  jointAgreement
  publicFact : RepresentationalType

record PromotionWitness
  (source target : RepresentationalType) : Set where
  constructor promotionWitness
  field evidence : Set

-- No generic coercion between representational types is provided.

------------------------------------------------------------------------
-- Behaviour and consent are non-identical.
------------------------------------------------------------------------

data BehaviourObservation : Set where
  performed
  silent
  withdrew
  froze : BehaviourObservation

data LatentChoiceState : Set where
  willing
  complyingUnderPressure
  submitted
  frozenWithoutChoice : LatentChoiceState

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
    refusalAvailable : Bool
    deferralAvailable : Bool
    capacityAvailable : Bool

open ConsentCounterfactual public

record ValidChoiceTransition : Set where
  constructor validChoiceTransition
  field
    latentState : LatentChoiceState
    counterfactual : ConsentCounterfactual
    refusalWasAvailable : refusalAvailable counterfactual ≡ true
    capacityWasAvailable : capacityAvailable counterfactual ≡ true

open ValidChoiceTransition public
