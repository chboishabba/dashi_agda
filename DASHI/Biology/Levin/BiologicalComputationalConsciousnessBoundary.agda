module DASHI.Biology.Levin.BiologicalComputationalConsciousnessBoundary where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)

import DASHI.Biology.Levin.SubstrateConstrainedComputation as Substrate
import DASHI.Biology.Levin.ObserverRelativePolycomputation as Observer
import DASHI.Biology.Levin.ConstitutiveInteractiveAutonomy as Autonomy
import DASHI.Biology.Levin.DurableIntegratedState as Durability
import DASHI.Biology.Levin.ProblemSpaceAgency as Problem

record ReadWriteExperienceCandidate : Set where
  field
    globallyAvailableReadSignal : Bool
    selfGeneratedActivity      : Bool
    actionSelection            : Bool
    actionConsequencesIntegrated : Bool
    selfOtherDiscrimination    : Bool
    memoryAcrossRelevantInterval : Bool
    counterfactualPerturbationSpecified : Bool

record ConsciousnessPromotionGate : Set where
  field
    operationalTargetDefined      : Bool
    substrateFeaturesSpecified    : Bool
    privilegedScaleJustified      : Bool
    observerDependenceControlled  : Bool
    autonomyMeasured              : Bool
    durableIntegrationMeasured    : Bool
    memoryRequirementTested       : Bool
    actionAndReceptionSeparated   : Bool
    reportChannelNotSoleEvidence  : Bool
    alternativeModelsCompared     : Bool
    promotionAllowed              : Bool

canonicalConsciousnessPromotionGate : ConsciousnessPromotionGate
canonicalConsciousnessPromotionGate = record
  { operationalTargetDefined = false
  ; substrateFeaturesSpecified = true
  ; privilegedScaleJustified = false
  ; observerDependenceControlled = false
  ; autonomyMeasured = false
  ; durableIntegrationMeasured = false
  ; memoryRequirementTested = false
  ; actionAndReceptionSeparated = true
  ; reportChannelNotSoleEvidence = true
  ; alternativeModelsCompared = false
  ; promotionAllowed = false
  }

record BiologicalComputationalConsciousnessBoundary : Set where
  field
    substrateBoundary : Substrate.SubstrateConstrainedComputationBoundary
    observerBoundary  : Observer.ObserverRelativePolycomputationBoundary
    autonomyBoundary  : Autonomy.ConstitutiveInteractiveAutonomyBoundary
    durabilityBoundary : Durability.DurableIntegratedStateBoundary
    problemSpaceBoundary : Problem.ProblemSpaceAgencyBoundary
    gate : ConsciousnessPromotionGate
    intelligenceNotSentience : Bool
    sentienceNotMetacognitiveSelfReport : Bool
    sameBehaviourNotSamePhenomenalStatus : Bool
    differentArchitectureNotProofOfDifferentStatus : Bool
    feltExperienceRemainsUnverified : Bool
    actionFirstModelRemainsCandidate : Bool
    noCurrentLLMConsciousnessClaim : Bool
    noBiologyOnlyConsciousnessClaim : Bool
    interpretation : String

canonicalBiologicalComputationalConsciousnessBoundary :
  BiologicalComputationalConsciousnessBoundary
canonicalBiologicalComputationalConsciousnessBoundary = record
  { substrateBoundary = Substrate.canonicalSubstrateConstrainedComputationBoundary
  ; observerBoundary = Observer.canonicalObserverRelativePolycomputationBoundary
  ; autonomyBoundary = Autonomy.canonicalConstitutiveInteractiveAutonomyBoundary
  ; durabilityBoundary = Durability.canonicalDurableIntegratedStateBoundary
  ; problemSpaceBoundary = Problem.canonicalProblemSpaceAgencyBoundary
  ; gate = canonicalConsciousnessPromotionGate
  ; intelligenceNotSentience = true
  ; sentienceNotMetacognitiveSelfReport = true
  ; sameBehaviourNotSamePhenomenalStatus = true
  ; differentArchitectureNotProofOfDifferentStatus = true
  ; feltExperienceRemainsUnverified = true
  ; actionFirstModelRemainsCandidate = true
  ; noCurrentLLMConsciousnessClaim = true
  ; noBiologyOnlyConsciousnessClaim = true
  ; interpretation = "Consciousness is not inferred from verbal output, analog dynamics, integration, autonomy, memory, biology or computation alone; candidate read and write capacities remain separated behind an explicit empirical gate"
  }
