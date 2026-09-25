module DASHI.Education.DigitalESDSituatedCapabilityEvidenceCrossPollinationExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)

import DASHI.Core.IntersectionalNonFactorability as INF
import DASHI.Education.CapabilityRecognitionExact as Capability
import DASHI.Education.SituatedRelationalLearningAffordanceExact as Affordance
import DASHI.Education.EarlyLearningCounterfactualHeterogeneityExact as Counterfactual
import DASHI.Education.CommunityConnectednessTopologyExact as Connectedness
import DASHI.Wikimedia.IbrahimSnowballTestimonyMemoryCredibilityCorroborationExpertBidiExact as Testimony
import DASHI.Wikimedia.IbrahimSnowballMemoryHyperfabricCollectiveOralHistoryBidiExact as Collective
import DASHI.Education.EducationSituatedInvestmentTrajectoryExact as Trajectory
import DASHI.Education.DigitalESDRelationalExternalityReturnBridgeExact as ReturnBridge

------------------------------------------------------------------------
-- DIGITAL-ESD SITUATED CAPABILITY / EVIDENCE CROSS-POLLINATION
--
-- Thin reuse layer.  The imported owners remain authoritative for their own
-- theorem surfaces.  This module only exposes distinctions needed by the
-- Digital-ESD situated trajectory:
--
--   capability != recognition
--   availability != reachability != contestability/agency
--   intervention label != counterfactual-relative effect
--   formal connection != effective connection != authority
--   report/testimony != memory reliability
--   report multiplicity != independent corroboration
--   collective narrative != individual latent memory state
--   remembered content != provenance/source origin
--
-- No source below is promoted into empirical authority for a named Digital-ESD
-- intervention merely by importing the structural theorem.
------------------------------------------------------------------------

canonicalCapabilityBoundary : Capability.CapabilityRecognitionBoundary
canonicalCapabilityBoundary = Capability.canonicalCapabilityRecognitionBoundary

canonicalAffordanceGate : Affordance.ReachableContestableAffordanceGate
canonicalAffordanceGate = Affordance.canonicalReachableContestableAffordanceGate

canonicalCounterfactualBoundary : Counterfactual.CounterfactualHeterogeneityBoundary
canonicalCounterfactualBoundary = Counterfactual.canonicalCounterfactualHeterogeneityBoundary

canonicalConnectednessBoundary : Connectedness.CommunityConnectednessBoundary
canonicalConnectednessBoundary = Connectedness.canonicalCommunityConnectednessBoundary

canonicalTestimonyBoundary : Testimony.TestimonyMemoryCredibilityBoundary
canonicalTestimonyBoundary = Testimony.canonicalTestimonyMemoryCredibilityBoundary

canonicalCollectiveMemoryBoundary : Collective.MemoryHyperfabricCollectiveOralBoundary
canonicalCollectiveMemoryBoundary =
  Collective.canonicalMemoryHyperfabricCollectiveOralBoundary

canonicalSituatedReturnBoundary :
  Trajectory.SituatedInvestmentTrajectoryBoundary
canonicalSituatedReturnBoundary =
  Trajectory.canonicalSituatedInvestmentTrajectoryBoundary

canonicalRelationalReturnBoundary :
  ReturnBridge.DigitalESDRelationalReturnBoundary
canonicalRelationalReturnBoundary =
  ReturnBridge.canonicalDigitalESDRelationalReturnBoundary

------------------------------------------------------------------------
-- Capability / recognition.
------------------------------------------------------------------------

capabilityCannotRecoverRecognition :
  INF.FactorsThrough
    Capability.capabilityProjection
    Capability.recognitionProjection
  → ⊥
capabilityCannotRecoverRecognition =
  Capability.capabilityAloneCannotDetermineRecognition

nonRecognitionCannotRecoverCapability :
  INF.FactorsThrough
    Capability.recognitionProjection
    Capability.capabilityProjection
  → ⊥
nonRecognitionCannotRecoverCapability =
  Capability.lackOfRecognitionCannotDetermineLackOfCapability

------------------------------------------------------------------------
-- Availability / reachability / contestability.
------------------------------------------------------------------------

availabilityCannotRecoverReachability :
  INF.FactorsThrough
    Affordance.availabilityProjection
    Affordance.reachabilityWitness
  → ⊥
availabilityCannotRecoverReachability =
  Affordance.availableAffordanceCannotDetermineReachability

reachabilityCannotRecoverContestableAgency :
  INF.FactorsThrough
    Affordance.reachableProjection
    Affordance.contestableAgencyWitness
  → ⊥
reachabilityCannotRecoverContestableAgency =
  Affordance.reachabilityCannotDetermineDevelopmentalAgency

------------------------------------------------------------------------
-- Counterfactual heterogeneity.
------------------------------------------------------------------------

interventionLabelCannotRecoverSituatedEffect :
  INF.FactorsThrough
    Counterfactual.interventionProjection
    Counterfactual.counterfactualRelativeEffect
  → ⊥
interventionLabelCannotRecoverSituatedEffect =
  Counterfactual.interventionLabelCannotDetermineEffect

observedGroupCannotRecoverIndividualEffect :
  INF.FactorsThrough
    Counterfactual.observedGroupProjection
    Counterfactual.withinGroupEffect
  → ⊥
observedGroupCannotRecoverIndividualEffect =
  Counterfactual.observedGroupCannotDetermineIndividualEffect

------------------------------------------------------------------------
-- Connectedness / authority.
------------------------------------------------------------------------

formalConnectionCannotRecoverEffectiveConnection :
  INF.FactorsThrough
    Connectedness.formalProjection
    Connectedness.effectiveProjection
  → ⊥
formalConnectionCannotRecoverEffectiveConnection =
  Connectedness.formalConnectionCannotDetermineEffectiveConnection

effectiveConnectionCannotRecoverAuthority :
  INF.FactorsThrough
    Connectedness.effectiveProjection
    Connectedness.authorityProjection
  → ⊥
effectiveConnectionCannotRecoverAuthority =
  Connectedness.effectiveConnectionCannotDetermineAuthority

sameBurdenCannotRecoverRelationalAffordance :
  INF.FactorsThrough
    Connectedness.burdenProjection
    Connectedness.dwellProjection
  → ⊥
sameBurdenCannotRecoverRelationalAffordance =
  Connectedness.travelBurdenCannotDetermineDwellAffordance

------------------------------------------------------------------------
-- Testimony / evidence / memory provenance.
------------------------------------------------------------------------

reportCannotRecoverMemoryReliability :
  INF.FactorsThrough Testimony.reportSurface Testimony.memoryStatus → ⊥
reportCannotRecoverMemoryReliability =
  Testimony.testimonyCannotFactorMemoryReliability

credibilityCannotRecoverTruth :
  INF.FactorsThrough Testimony.credibilitySurface Testimony.propositionTruth → ⊥
credibilityCannotRecoverTruth =
  Testimony.credibilityCannotFactorTruth

reportMultiplicityCannotRecoverIndependentCorroboration :
  INF.FactorsThrough Testimony.countSurface Testimony.independenceStatus → ⊥
reportMultiplicityCannotRecoverIndependentCorroboration =
  Testimony.reportMultiplicityCannotFactorIndependence

collectiveNarrativeCannotRecoverIndividualMemory :
  INF.FactorsThrough
    Collective.collectiveNarrativeSurface
    Collective.individualMemoryState
  → ⊥
collectiveNarrativeCannotRecoverIndividualMemory =
  Collective.collectiveNarrativeCannotFactorIndividualMemoryState

rememberedContentCannotRecoverMemoryOrigin :
  INF.FactorsThrough
    Collective.rememberedSurface
    Collective.memoryOrigin
  → ⊥
rememberedContentCannotRecoverMemoryOrigin =
  Collective.rememberedSurfaceCannotFactorSourceOrigin

------------------------------------------------------------------------
-- Digital-ESD-specific non-promotion gates.
------------------------------------------------------------------------

data HighReturnMeansCapabilityPresent : Set where
data HighReturnMeansCapabilityRecognised : Set where
data TechnologyAvailableMeansReachable : Set where
data TechnologyReachableMeansContestableAgency : Set where
data SameInterventionMeansSameEffect : Set where
data GroupAverageMeansIndividualEffect : Set where
data FormalParticipationMeansEffectiveConnection : Set where
data EffectiveConnectionMeansAuthority : Set where
data LearnerReportMeansLatentMemoryTruth : Set where
data RepeatedReportMeansIndependentCorroboration : Set where
data CollectiveNarrativeMeansIndividualState : Set where
data RememberedContentMeansDirectExperience : Set where

highReturnDoesNotCreateCapability :
  HighReturnMeansCapabilityPresent → ⊥
highReturnDoesNotCreateCapability ()

highReturnDoesNotCreateRecognition :
  HighReturnMeansCapabilityRecognised → ⊥
highReturnDoesNotCreateRecognition ()

availabilityDoesNotCreateReachability :
  TechnologyAvailableMeansReachable → ⊥
availabilityDoesNotCreateReachability ()

reachabilityDoesNotCreateContestableAgency :
  TechnologyReachableMeansContestableAgency → ⊥
reachabilityDoesNotCreateContestableAgency ()

sameInterventionDoesNotCreateSameEffect :
  SameInterventionMeansSameEffect → ⊥
sameInterventionDoesNotCreateSameEffect ()

groupAverageDoesNotCreateIndividualEffect :
  GroupAverageMeansIndividualEffect → ⊥
groupAverageDoesNotCreateIndividualEffect ()

formalParticipationDoesNotCreateEffectiveConnection :
  FormalParticipationMeansEffectiveConnection → ⊥
formalParticipationDoesNotCreateEffectiveConnection ()

effectiveConnectionDoesNotCreateAuthority :
  EffectiveConnectionMeansAuthority → ⊥
effectiveConnectionDoesNotCreateAuthority ()

learnerReportDoesNotCreateLatentMemoryTruth :
  LearnerReportMeansLatentMemoryTruth → ⊥
learnerReportDoesNotCreateLatentMemoryTruth ()

repeatedReportDoesNotCreateIndependentCorroboration :
  RepeatedReportMeansIndependentCorroboration → ⊥
repeatedReportDoesNotCreateIndependentCorroboration ()

collectiveNarrativeDoesNotCreateIndividualState :
  CollectiveNarrativeMeansIndividualState → ⊥
collectiveNarrativeDoesNotCreateIndividualState ()

rememberedContentDoesNotCreateDirectExperience :
  RememberedContentMeansDirectExperience → ⊥
rememberedContentDoesNotCreateDirectExperience ()

record DigitalESDSituatedCapabilityEvidenceBoundary : Set where
  constructor digital-esd-situated-capability-evidence-boundary
  field
    capabilityEqualsRecognition : Bool
    capabilityEqualsRecognitionIsFalse : capabilityEqualsRecognition ≡ false

    availabilityEqualsReachability : Bool
    availabilityEqualsReachabilityIsFalse : availabilityEqualsReachability ≡ false

    reachabilityEqualsContestableAgency : Bool
    reachabilityEqualsContestableAgencyIsFalse :
      reachabilityEqualsContestableAgency ≡ false

    interventionLabelDeterminesSituatedEffect : Bool
    interventionLabelDeterminesSituatedEffectIsFalse :
      interventionLabelDeterminesSituatedEffect ≡ false

    observedGroupDeterminesIndividualEffect : Bool
    observedGroupDeterminesIndividualEffectIsFalse :
      observedGroupDeterminesIndividualEffect ≡ false

    formalConnectionEqualsEffectiveConnection : Bool
    formalConnectionEqualsEffectiveConnectionIsFalse :
      formalConnectionEqualsEffectiveConnection ≡ false

    effectiveConnectionDeterminesAuthority : Bool
    effectiveConnectionDeterminesAuthorityIsFalse :
      effectiveConnectionDeterminesAuthority ≡ false

    learnerReportDeterminesLatentMemoryReliability : Bool
    learnerReportDeterminesLatentMemoryReliabilityIsFalse :
      learnerReportDeterminesLatentMemoryReliability ≡ false

    repeatedReportsDetermineIndependentCorroboration : Bool
    repeatedReportsDetermineIndependentCorroborationIsFalse :
      repeatedReportsDetermineIndependentCorroboration ≡ false

    collectiveNarrativeDeterminesIndividualMemory : Bool
    collectiveNarrativeDeterminesIndividualMemoryIsFalse :
      collectiveNarrativeDeterminesIndividualMemory ≡ false

    rememberedContentDeterminesSourceOrigin : Bool
    rememberedContentDeterminesSourceOriginIsFalse :
      rememberedContentDeterminesSourceOrigin ≡ false

canonicalDigitalESDSituatedCapabilityEvidenceBoundary :
  DigitalESDSituatedCapabilityEvidenceBoundary
canonicalDigitalESDSituatedCapabilityEvidenceBoundary =
  digital-esd-situated-capability-evidence-boundary
    false refl
    false refl
    false refl
    false refl
    false refl
    false refl
    false refl
    false refl
    false refl
    false refl
    false refl
