module DASHI.Education.DigitalESDSituatedCapabilityEvidenceCrossPollinationRegression where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)

import DASHI.Core.IntersectionalNonFactorability as INF
import DASHI.Education.DigitalESDSituatedCapabilityEvidenceCrossPollinationExact as Bridge
import DASHI.Education.CapabilityRecognitionExact as Capability
import DASHI.Education.SituatedRelationalLearningAffordanceExact as Affordance
import DASHI.Education.EarlyLearningCounterfactualHeterogeneityExact as Counterfactual
import DASHI.Education.CommunityConnectednessTopologyExact as Connectedness
import DASHI.Wikimedia.IbrahimSnowballTestimonyMemoryCredibilityCorroborationExpertBidiExact as Testimony
import DASHI.Wikimedia.IbrahimSnowballMemoryHyperfabricCollectiveOralHistoryBidiExact as Collective

capabilityRecognitionRegression :
  INF.FactorsThrough Capability.capabilityProjection Capability.recognitionProjection → ⊥
capabilityRecognitionRegression = Bridge.capabilityCannotRecoverRecognition

availabilityReachabilityRegression :
  INF.FactorsThrough Affordance.availabilityProjection Affordance.reachabilityWitness → ⊥
availabilityReachabilityRegression = Bridge.availabilityCannotRecoverReachability

reachabilityAgencyRegression :
  INF.FactorsThrough Affordance.reachableProjection Affordance.contestableAgencyWitness → ⊥
reachabilityAgencyRegression = Bridge.reachabilityCannotRecoverContestableAgency

counterfactualEffectRegression :
  INF.FactorsThrough Counterfactual.interventionProjection Counterfactual.counterfactualRelativeEffect → ⊥
counterfactualEffectRegression = Bridge.interventionLabelCannotRecoverSituatedEffect

subgroupEffectRegression :
  INF.FactorsThrough Counterfactual.observedGroupProjection Counterfactual.withinGroupEffect → ⊥
subgroupEffectRegression = Bridge.observedGroupCannotRecoverIndividualEffect

formalConnectionRegression :
  INF.FactorsThrough Connectedness.formalProjection Connectedness.effectiveProjection → ⊥
formalConnectionRegression = Bridge.formalConnectionCannotRecoverEffectiveConnection

connectionAuthorityRegression :
  INF.FactorsThrough Connectedness.effectiveProjection Connectedness.authorityProjection → ⊥
connectionAuthorityRegression = Bridge.effectiveConnectionCannotRecoverAuthority

testimonyMemoryRegression :
  INF.FactorsThrough Testimony.reportSurface Testimony.memoryStatus → ⊥
testimonyMemoryRegression = Bridge.reportCannotRecoverMemoryReliability

corroborationRegression :
  INF.FactorsThrough Testimony.countSurface Testimony.independenceStatus → ⊥
corroborationRegression = Bridge.reportMultiplicityCannotRecoverIndependentCorroboration

collectiveMemoryRegression :
  INF.FactorsThrough Collective.collectiveNarrativeSurface Collective.individualMemoryState → ⊥
collectiveMemoryRegression = Bridge.collectiveNarrativeCannotRecoverIndividualMemory

memoryOriginRegression :
  INF.FactorsThrough Collective.rememberedSurface Collective.memoryOrigin → ⊥
memoryOriginRegression = Bridge.rememberedContentCannotRecoverMemoryOrigin

capabilityOwnerRegression :
  Bridge.canonicalCapabilityBoundary ≡ Capability.canonicalCapabilityRecognitionBoundary
capabilityOwnerRegression = refl

affordanceOwnerRegression :
  Bridge.canonicalAffordanceGate ≡ Affordance.canonicalReachableContestableAffordanceGate
affordanceOwnerRegression = refl

counterfactualOwnerRegression :
  Bridge.canonicalCounterfactualBoundary
  ≡ Counterfactual.canonicalCounterfactualHeterogeneityBoundary
counterfactualOwnerRegression = refl

connectednessOwnerRegression :
  Bridge.canonicalConnectednessBoundary
  ≡ Connectedness.canonicalCommunityConnectednessBoundary
connectednessOwnerRegression = refl

testimonyOwnerRegression :
  Bridge.canonicalTestimonyBoundary
  ≡ Testimony.canonicalTestimonyMemoryCredibilityBoundary
testimonyOwnerRegression = refl

collectiveOwnerRegression :
  Bridge.canonicalCollectiveMemoryBoundary
  ≡ Collective.canonicalMemoryHyperfabricCollectiveOralBoundary
collectiveOwnerRegression = refl
