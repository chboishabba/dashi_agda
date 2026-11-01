module DASHI.Biology.Levin.HostManipulationCausalSpectrum where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)

import DASHI.Biology.Levin.ComponentCausalRoleBoundary as Causal
import DASHI.Biology.Levin.MicrobiomeHostAppetiteBoundary as Appetite
import DASHI.Biology.Levin.ProblemSpaceAgency as Problem

record HostManipulationProtocol : Set where
  field
    manipulatorSpecified : Bool
    hostBehaviourSpecified : Bool
    baselineBehaviourMeasured : Bool
    manipulatorRemovalOrBlockadeAttempted : Bool
    sufficiencyTransferAttempted : Bool
    hostDamageSeparated : Bool
    rewardOrValuationShiftMeasured : Bool
    motorExecutionShiftMeasured : Bool
    transmissionBenefitMeasured : Bool
    alternativeHostResponseModelCompared : Bool

record HostManipulationCausalSpectrum : Set where
  field
    causalRoleBoundary : Causal.ComponentCausalRoleBoundary
    appetiteBoundary : Appetite.MicrobiomeHostAppetiteBoundary
    problemSpaceBoundary : Problem.ProblemSpaceAgencyBoundary
    signallingLevelSeparated : Bool
    biasLevelSeparated : Bool
    incentiveModificationSeparated : Bool
    compulsionSeparated : Bool
    motorTakeoverSeparated : Bool
    hostPathologyNotManipulationByDefinition : Bool
    manipulatorFitnessBenefitRequiresMeasurement : Bool
    ordinaryMicrobiomeInfluenceNotTakeover : Bool
    interpretation : String

canonicalHostManipulationCausalSpectrum : HostManipulationCausalSpectrum
canonicalHostManipulationCausalSpectrum = record
  { causalRoleBoundary = Causal.canonicalComponentCausalRoleBoundary
  ; appetiteBoundary = Appetite.canonicalMicrobiomeHostAppetiteBoundary
  ; problemSpaceBoundary = Problem.canonicalProblemSpaceAgencyBoundary
  ; signallingLevelSeparated = true
  ; biasLevelSeparated = true
  ; incentiveModificationSeparated = true
  ; compulsionSeparated = true
  ; motorTakeoverSeparated = true
  ; hostPathologyNotManipulationByDefinition = true
  ; manipulatorFitnessBenefitRequiresMeasurement = true
  ; ordinaryMicrobiomeInfluenceNotTakeover = true
  ; interpretation = "Cross-organism behavioural effects are graded from signalling and bias through incentive modification, compulsion and motor takeover; manipulation additionally requires causal intervention and evidence that the altered policy serves the candidate manipulator rather than merely reflecting host damage"
  }
