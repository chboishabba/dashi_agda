module DASHI.Reasoning.MaleCNSJointConsumerBidiRefinementExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.IntersectionalNonFactorability as NF
import DASHI.Biology.FunctionalConnectomeBodyMemoryBridge as Connectome
import DASHI.Biology.IntersectionalLongitudinalProxyTransitionBridge as Longitudinal
import DASHI.Biology.AnimalexicDrosophilaEmbodiedBridge as Animalexic
import DASHI.Reasoning.MaleCNSLatentStateMoEGrokkingAnimalexicCrossPollinationExact as Latent

------------------------------------------------------------------------
-- MALECNS JOINT-CONSUMER BIDI REFINEMENT
--
-- Forward direction:
--   connectome / functional / longitudinal observations constrain candidate
--   latent representations, but do not invert uniquely to hidden state.
--
-- Backward direction:
--   a consumer or admissible-intervention collision is a typed obligation to
--   refine the latent observer locally.  It is not permission to manufacture
--   an unobserved biological mechanism.
------------------------------------------------------------------------

------------------------------------------------------------------------
-- Finite specimen: same choice, different memory.
------------------------------------------------------------------------

data HiddenState : Set where
  chooseArememberA : HiddenState
  chooseArememberB : HiddenState

data ChoiceOnlyLatent : Set where
  chooseA : ChoiceOnlyLatent

choiceProjection : HiddenState → ChoiceOnlyLatent
choiceProjection chooseArememberA = chooseA
choiceProjection chooseArememberB = chooseA

data ChoiceMemoryOutcome : Set where
  choseAWithMemoryA : ChoiceMemoryOutcome
  choseAWithMemoryB : ChoiceMemoryOutcome

jointChoiceMemoryOutcome : HiddenState → ChoiceMemoryOutcome
jointChoiceMemoryOutcome chooseArememberA = choseAWithMemoryA
jointChoiceMemoryOutcome chooseArememberB = choseAWithMemoryB

jointChoiceMemoryOutcomeDiffers :
  jointChoiceMemoryOutcome chooseArememberA ≡
  jointChoiceMemoryOutcome chooseArememberB → ⊥
jointChoiceMemoryOutcomeDiffers ()

choiceOnlyJointConsumerCollision :
  NF.NonFactorabilityWitness choiceProjection jointChoiceMemoryOutcome
choiceOnlyJointConsumerCollision =
  NF.nonFactorabilityWitness
    chooseArememberA
    chooseArememberB
    refl
    jointChoiceMemoryOutcomeDiffers

choiceOnlyCannotFactorJointOutcome :
  NF.FactorsThrough choiceProjection jointChoiceMemoryOutcome → ⊥
choiceOnlyCannotFactorJointOutcome =
  NF.witnessRulesOutEveryFlatFactorisation
    choiceOnlyJointConsumerCollision

choiceRechartCannotRecoverMemory :
  ∀ {Recharted : Set} →
  (rechart : ChoiceOnlyLatent → Recharted) →
  NF.FactorsThrough
    (λ state → rechart (choiceProjection state))
    jointChoiceMemoryOutcome → ⊥
choiceRechartCannotRecoverMemory rechart =
  NF.rechartingCannotRecoverErasedPhenomenon
    rechart choiceOnlyJointConsumerCollision

------------------------------------------------------------------------
-- Local repair: add exactly the missing memory distinction.
------------------------------------------------------------------------

data RepairedLatent : Set where
  chooseAwithMemoryA : RepairedLatent
  chooseAwithMemoryB : RepairedLatent

repairedProjection : HiddenState → RepairedLatent
repairedProjection chooseArememberA = chooseAwithMemoryA
repairedProjection chooseArememberB = chooseAwithMemoryB

interpretRepairedLatent : RepairedLatent → ChoiceMemoryOutcome
interpretRepairedLatent chooseAwithMemoryA = choseAWithMemoryA
interpretRepairedLatent chooseAwithMemoryB = choseAWithMemoryB

repairedLatentFactorsJointOutcome :
  NF.FactorsThrough repairedProjection jointChoiceMemoryOutcome
repairedLatentFactorsJointOutcome =
  NF.factorsThrough
    interpretRepairedLatent
    (λ
      { chooseArememberA → refl
      ; chooseArememberB → refl
      })

------------------------------------------------------------------------
-- Bidi refinement obligation.
------------------------------------------------------------------------

data RefinementObligation : Set where
  addConsumerSeparatingFibre : RefinementObligation

interventionFailureCreatesRefinementObligation :
  ∀ {Situated Flat Outcome : Set}
    {flatten : Situated → Flat}
    {phenomenon : Situated → Outcome} →
  NF.NonFactorabilityWitness flatten phenomenon →
  RefinementObligation
interventionFailureCreatesRefinementObligation _ =
  addConsumerSeparatingFibre

choiceCollisionCreatesRefinementObligation : RefinementObligation
choiceCollisionCreatesRefinementObligation =
  interventionFailureCreatesRefinementObligation
    choiceOnlyJointConsumerCollision

------------------------------------------------------------------------
-- Broader connectome / longitudinal donors.
------------------------------------------------------------------------

connectomeConstraintIsNotLatentInversion :
  Connectome.reverseInferenceAuthorityBlocked
    Connectome.canonicalFunctionalConnectomeBodyMemoryBridge ≡ false
connectomeConstraintIsNotLatentInversion =
  Connectome.reverseInferenceAuthorityBlockedIsFalse
    Connectome.canonicalFunctionalConnectomeBodyMemoryBridge

connectomeCarrierRemainsProxyNotIdentity :
  Connectome.proxyNotIdentity
    (Connectome.connectomeCarrier
      Connectome.canonicalFunctionalConnectomeBodyMemoryBridge) ≡ true
connectomeCarrierRemainsProxyNotIdentity =
  Connectome.proxyNotIdentityIsTrue
    (Connectome.connectomeCarrier
      Connectome.canonicalFunctionalConnectomeBodyMemoryBridge)

populationTrajectoryDoesNotPromoteMechanism :
  Longitudinal.observationMechanismPromoted
    Longitudinal.canonicalPopulationTrajectoryObservation ≡ false
populationTrajectoryDoesNotPromoteMechanism =
  Longitudinal.canonicalPopulationTrajectoryDoesNotPromoteMechanism

longitudinalTransitionChangesAdmissibleStructure :
  Longitudinal.transitionChangesAdmissibleStructure
    Longitudinal.canonicalConsentGovernedPlusOneTransition ≡ true
longitudinalTransitionChangesAdmissibleStructure =
  Longitudinal.canonicalPlusOneChangesTransitionsNotTruth

------------------------------------------------------------------------
-- Exact Drosophila/Animalexic interpretation boundaries stay in force.
------------------------------------------------------------------------

canonicalAnimalexicDrosophilaBoundaries :
  List Animalexic.DrosophilaAnimalexicBoundary
canonicalAnimalexicDrosophilaBoundaries =
  Animalexic.canonicalDrosophilaAnimalexicBoundaries

------------------------------------------------------------------------
-- Aggregate bidi boundary.
------------------------------------------------------------------------

record ConnectomeLatentBidiBoundary : Set where
  constructor connectome-latent-bidi-boundary
  field
    connectomeConstrainsCandidateLatent : Bool
    connectomeConstrainsCandidateLatentIsTrue :
      connectomeConstrainsCandidateLatent ≡ true

    consumerCollisionForcesRefinementObligation : Bool
    consumerCollisionForcesRefinementObligationIsTrue :
      consumerCollisionForcesRefinementObligation ≡ true

    postRechartRecoversErasedMemory : Bool
    postRechartRecoversErasedMemoryIsFalse :
      postRechartRecoversErasedMemory ≡ false

    repairedLatentPaysFiniteJointConsumer : Bool
    repairedLatentPaysFiniteJointConsumerIsTrue :
      repairedLatentPaysFiniteJointConsumer ≡ true

    connectomeConstraintEqualsHiddenStateInversion : Bool
    connectomeConstraintEqualsHiddenStateInversionIsFalse :
      connectomeConstraintEqualsHiddenStateInversion ≡ false

    trajectoryEvidenceEqualsMechanism : Bool
    trajectoryEvidenceEqualsMechanismIsFalse :
      trajectoryEvidenceEqualsMechanism ≡ false

    refinementObligationEqualsBiologicalMechanismDiscovery : Bool
    refinementObligationEqualsBiologicalMechanismDiscoveryIsFalse :
      refinementObligationEqualsBiologicalMechanismDiscovery ≡ false

    finiteSpecimenEqualsEmpiricalMaleCNSAffectResult : Bool
    finiteSpecimenEqualsEmpiricalMaleCNSAffectResultIsFalse :
      finiteSpecimenEqualsEmpiricalMaleCNSAffectResult ≡ false

    interpretation : String

open ConnectomeLatentBidiBoundary public

canonicalConnectomeLatentBidiBoundary : ConnectomeLatentBidiBoundary
canonicalConnectomeLatentBidiBoundary =
  connectome-latent-bidi-boundary
    true refl
    true refl
    false refl
    true refl
    false refl
    false refl
    false refl
    false refl
    "Bidi discipline: connectome/proxy observations constrain candidate latent state forward; consumer/intervention collisions flow backward only as local refinement obligations. Neither direction supplies hidden-state inversion, mechanism, affect semantics, or subjective phenomenology."
