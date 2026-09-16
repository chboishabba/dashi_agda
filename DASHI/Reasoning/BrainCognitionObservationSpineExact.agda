module DASHI.Reasoning.BrainCognitionObservationSpineExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.ConsumerFamilyRefinementKernelExact as Family
import DASHI.Core.IntersectionalNonFactorability as NF
import DASHI.Cognition.PNF.MemoryFibre as Memory
import DASHI.Cognition.PNF.LearningAlgebra as Learning
import DASHI.Cognition.PNF.DecisionActionProjectionNonFactorabilityExact as Decision
import DASHI.Physics.Closure.BrainConnectomeFMRIObservationQuotient as Brain
import DASHI.Reasoning.AuthorityBooleanPolarityRepairExact as Authority
import DASHI.Reasoning.MaleCNSConsumerRelativeLatentParetoExact as Pareto
import DASHI.Reasoning.MaleCNSLatentStateMoEGrokkingAnimalexicCrossPollinationExact as Programme

------------------------------------------------------------------------
-- BRAIN / COGNITION / OBSERVATION SPINE
--
-- Existing MaleCNS Z_d is a consumer-relative structure/function code.  This
-- owner asks which *additional* latent questions could factor through a code.
-- It does not identify the current structural latent with memory, motor policy,
-- decision state, semantic content, mechanism, or subjective state.
------------------------------------------------------------------------

data CognitionConsumer : Set where
  rememberedEventConsumer : CognitionConsumer
  memoryInfluenceConsumer : CognitionConsumer
  motorPolicyConsumer : CognitionConsumer
  fineDecisionStateConsumer : CognitionConsumer
  futureActionConsumer : CognitionConsumer
  functionalObservationConsumer : CognitionConsumer

CognitionConsumerFamily : Set → Set₁
CognitionConsumerFamily State = Family.ConsumerFamily State CognitionConsumer

CognitionCodeAdequacy :
  ∀ {State Code : Set} →
  (encode : State → Code) →
  CognitionConsumerFamily State →
  Set₁
CognitionCodeAdequacy = Family.FamilyFactorsThrough

consumerAdequacyFromWholeFamily :
  ∀ {State Code}
    {encode : State → Code}
    {family : CognitionConsumerFamily State} →
  CognitionCodeAdequacy encode family →
  (consumer : CognitionConsumer) →
  NF.FactorsThrough encode (Family.observe family consumer)
consumerAdequacyFromWholeFamily = Family.consumerFactor

------------------------------------------------------------------------
-- Existing paid cognition anchors.
------------------------------------------------------------------------

memoryContentMayPersistWhileInfluenceChanges :
  ∀ memory →
  Memory.rememberedEvent (Memory.extinguishActionDominance memory)
  ≡ Memory.rememberedEvent memory
memoryContentMayPersistWhileInfluenceChanges =
  Memory.extinctionPreservesRememberedEvent

extinctionLearningPreservesSemanticContent :
  ∀ memory →
  Learning.publicSemanticContentPreserved (Learning.extinctionReceipt memory)
  ≡ true
extinctionLearningPreservesSemanticContent memory =
  Learning.publicSemanticContentPreservedIsTrue (Learning.extinctionReceipt memory)

observedActionDoesNotFactorFineDecisionState :
  NF.FactorsThrough Decision.observedAction Decision.fineDecisionState → ⊥
observedActionDoesNotFactorFineDecisionState =
  Decision.actionCannotRecoverFineDecisionState

highResolutionImagingIsObservationChannel :
  Brain.highResolutionFMRIIsObservationChannel
    Brain.canonicalBrainConnectomeFMRIObservationBoundary
  ≡ true
highResolutionImagingIsObservationChannel =
  Brain.highResolutionFMRIIsObservationChannelIsTrue
    Brain.canonicalBrainConnectomeFMRIObservationBoundary

------------------------------------------------------------------------
-- Current MaleCNS learned/derived structural latent receipt.
------------------------------------------------------------------------

currentD2LowestObservedDiscoveryMAE :
  Pareto.d2LowestObservedMAE Pareto.currentPythonLatentDiscoveryRuntimeReceipt
  ≡ true
currentD2LowestObservedDiscoveryMAE = refl

currentD2DoesNotDominateSenderGainAcrossMetrics :
  Pareto.d2DominatesSenderGainAcrossReportedMetrics
    Pareto.currentPythonLatentDiscoveryRuntimeReceipt
  ≡ false
currentD2DoesNotDominateSenderGainAcrossMetrics = refl

currentD2DoesNotPromoteUniversalMinimum :
  Pareto.discoveryBestDimensionPromotesUniversalMinimum
    Pareto.currentPythonLatentDiscoveryRuntimeReceipt
  ≡ false
currentD2DoesNotPromoteUniversalMinimum = refl

------------------------------------------------------------------------
-- Gauthey behavior observation acquisition coordinate.
--
-- Source-bounded paper facts: adult behaving flies were recorded on an
-- air-suspended ball; ball motion was acquired at 100 Hz and locomotion was
-- extracted with FicTrac; stimulus delivery and behavioral quantification were
-- synchronized.  The exact deposited behavior member and same-trial timebase
-- binding remain acquisition obligations in dashiBRAIN.
------------------------------------------------------------------------

record GautheyBehaviorObservationFrontier : Set where
  constructor gauthey-behavior-observation-frontier
  field
    paperDoi : String
    behavingFlyRecordingReported : Bool
    ballTracking100HzReported : Bool
    fictracLocomotionReported : Bool
    stimulusBehaviorSynchronizationReported : Bool
    gautheyBehaviorRecordedAndSynchronized : Bool
    behaviorResolverSource : String
    behaviorResolverSourceWritten : Bool
    exactBehaviorDepositMemberResolved : Bool
    exactTrialBehaviorBindingPaid : Bool
    neuralBehaviorTimebaseReceiptPaid : Bool
    motorPolicyDecoderPaid : Bool
    interpretation : String

open GautheyBehaviorObservationFrontier public

currentGautheyBehaviorObservationFrontier : GautheyBehaviorObservationFrontier
currentGautheyBehaviorObservationFrontier = gauthey-behavior-observation-frontier
  "10.1038/s41467-026-72437-1"
  true
  true
  true
  true
  true
  "dashiBRAIN:scripts/resolve_gauthey_behavior_sources.py"
  true
  false
  false
  false
  false
  "The publication pays existence of synchronized locomotor behavior recording, not the exact deposited behavior artifact or a motor-policy latent. The next empirical seam is archive-member identity plus same-trial neural/behavior timebase binding."

------------------------------------------------------------------------
-- Non-promotion firewalls.
------------------------------------------------------------------------

data StructuralLatentIsMemoryContent : Set where
structuralLatentDoesNotBecomeMemoryContent : StructuralLatentIsMemoryContent → ⊥
structuralLatentDoesNotBecomeMemoryContent ()

data StructuralLatentIsMotorPolicy : Set where
structuralLatentDoesNotBecomeMotorPolicy : StructuralLatentIsMotorPolicy → ⊥
structuralLatentDoesNotBecomeMotorPolicy ()

data StructuralLatentDimensionIsPhysicalBrainDimension : Set where
structuralLatentDimensionDoesNotIdentifyPhysicalBrainDimension :
  StructuralLatentDimensionIsPhysicalBrainDimension → ⊥
structuralLatentDimensionDoesNotIdentifyPhysicalBrainDimension ()

data ObservationEqualityImpliesLatentIdentity : Set where
observationEqualityDoesNotAuthorizeLatentIdentity :
  ObservationEqualityImpliesLatentIdentity → ⊥
observationEqualityDoesNotAuthorizeLatentIdentity ()

------------------------------------------------------------------------
-- Current missing-field frontier.
------------------------------------------------------------------------

record BrainCognitionObservationBoundary : Set where
  constructor brain-cognition-observation-boundary
  field
    cognitionUsesExistingConsumerFamilyKernel : Bool
    cognitionUsesExistingConsumerFamilyKernelIsTrue :
      cognitionUsesExistingConsumerFamilyKernel ≡ true

    currentStructuralLatentRuntimeObserved : Bool
    currentStructuralLatentRuntimeObservedIsTrue :
      currentStructuralLatentRuntimeObserved ≡ true

    currentD2IsDiscoveryMAECoordinate : Bool
    currentD2IsDiscoveryMAECoordinateIsTrue :
      currentD2IsDiscoveryMAECoordinate ≡ true

    currentStructuralLatentFactorsWholeCognitionFamily : Bool
    currentStructuralLatentFactorsWholeCognitionFamilyIsFalse :
      currentStructuralLatentFactorsWholeCognitionFamily ≡ false

    rememberedEventFactorisationPaid : Bool
    rememberedEventFactorisationPaidIsFalse :
      rememberedEventFactorisationPaid ≡ false

    memoryInfluenceFactorisationPaid : Bool
    memoryInfluenceFactorisationPaidIsFalse :
      memoryInfluenceFactorisationPaid ≡ false

    motorPolicyFactorisationPaid : Bool
    motorPolicyFactorisationPaidIsFalse :
      motorPolicyFactorisationPaid ≡ false

    fineDecisionStateFromActionFactorisationPaid : Bool
    fineDecisionStateFromActionFactorisationPaidIsFalse :
      fineDecisionStateFromActionFactorisationPaid ≡ false

    minimalLearnedLatentExtractionPaid : Bool
    minimalLearnedLatentExtractionPaidIsFalse :
      minimalLearnedLatentExtractionPaid ≡ false

    exactBehaviorObservationArtifactPaid : Bool
    exactBehaviorObservationArtifactPaidIsFalse :
      exactBehaviorObservationArtifactPaid ≡ false

    ninetyPercentUnusedBrainClaimPaid : Bool
    ninetyPercentUnusedBrainClaimPaidIsFalse :
      ninetyPercentUnusedBrainClaimPaid ≡ false

    structuralLatentDimensionEqualsPhysicalBrainDimension : Bool
    structuralLatentDimensionEqualsPhysicalBrainDimensionIsFalse :
      structuralLatentDimensionEqualsPhysicalBrainDimension ≡ false

    consumerMinimalCodeMayBeLowerDimensionalThanFineState : Bool
    consumerMinimalCodeMayBeLowerDimensionalThanFineStateIsTrue :
      consumerMinimalCodeMayBeLowerDimensionalThanFineState ≡ true

    authorityPolarityRepairConsumed : Bool
    authorityPolarityRepairConsumedIsTrue :
      authorityPolarityRepairConsumed ≡ true

    interpretation : String

open BrainCognitionObservationBoundary public

canonicalBrainCognitionObservationBoundary : BrainCognitionObservationBoundary
canonicalBrainCognitionObservationBoundary = brain-cognition-observation-boundary
  true refl
  true refl
  true refl
  false refl
  false refl
  false refl
  false refl
  false refl
  false refl
  false refl
  false refl
  false refl
  true refl
  true refl
  "The executed Z_d ladder is a structure/function consumer-relative latent search. Z2 currently has the lowest discovery MAE but is not a whole-cognition latent and is not identified with memory, motor policy, fine decision state, semantic content, or a physical two-dimensional brain state. A genuinely learned/internal latent becomes extractable only for the consumers whose outcomes factor through the proposed code."

authorityBoundary : Authority.AuthorityBooleanPolarityRepair
authorityBoundary = Authority.canonicalAuthorityBooleanPolarityRepair

programmeBoundary : Programme.LatentStateProgrammeBoundary
programmeBoundary = Programme.canonicalLatentStateProgrammeBoundary
