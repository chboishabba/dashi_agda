module DASHI.Biology.Levin.PhysarumMechanochemicalDecisionBoundary where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)

import DASHI.Biology.Levin.ProblemSpaceAgency as Problem
import DASHI.Biology.Levin.ConstitutiveInteractiveAutonomy as Autonomy
import DASHI.Biology.Levin.TravelingWaveComputationBoundary as Wave

record PhysarumDecisionProtocol : Set where
  field
    alternativesSpecified : Bool
    attractantAndRepellentFieldsMeasured : Bool
    contractionDynamicsMeasured : Bool
    cytoplasmicFlowMeasured : Bool
    networkTopologyMeasured : Bool
    choiceLatencyMeasured : Bool
    perturbationOfFlowAttempted : Bool
    passiveGradientExplanationCompared : Bool
    repeatedChoiceHistoryMeasured : Bool

record PhysarumMechanochemicalDecisionBoundary : Set where
  field
    problemSpaceBoundary : Problem.ProblemSpaceAgencyBoundary
    autonomyBoundary : Autonomy.ConstitutiveInteractiveAutonomyBoundary
    travelingWaveBoundary : Wave.TravelingWaveBoundary
    decisionNeedNotBeNeural : Bool
    morphologyMayParticipateInComputation : Bool
    contractionFlowAndTopologyCoupled : Bool
    gradientFollowingNotGeneralIntelligence : Bool
    mazeSolutionNotPlanningByDefinition : Bool
    causalDecisionClaimRequiresMechanochemicalPerturbation : Bool
    interpretation : String

canonicalPhysarumMechanochemicalDecisionBoundary : PhysarumMechanochemicalDecisionBoundary
canonicalPhysarumMechanochemicalDecisionBoundary = record
  { problemSpaceBoundary = Problem.canonicalProblemSpaceAgencyBoundary
  ; autonomyBoundary = Autonomy.canonicalConstitutiveInteractiveAutonomyBoundary
  ; travelingWaveBoundary = Wave.canonicalTravelingWaveBoundary
  ; decisionNeedNotBeNeural = true
  ; morphologyMayParticipateInComputation = true
  ; contractionFlowAndTopologyCoupled = true
  ; gradientFollowingNotGeneralIntelligence = true
  ; mazeSolutionNotPlanningByDefinition = true
  ; causalDecisionClaimRequiresMechanochemicalPerturbation = true
  ; interpretation = "Physarum choice is modelled through coupled contraction waves, cytoplasmic flow and network remodelling across explicit alternatives; successful navigation can witness decentralized decision dynamics without establishing neural planning or general intelligence"
  }
