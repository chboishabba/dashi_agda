module DASHI.Biology.Levin.FungalNetworkAgencyBoundary where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)

import DASHI.Biology.Levin.ProblemSpaceAgency as Problem
import DASHI.Biology.Levin.ConstitutiveInteractiveAutonomy as Autonomy
import DASHI.Biology.Levin.TravelingWaveComputationBoundary as Wave

record FungalNetworkObservation : Set where
  field
    distributedGrowthMeasured : Bool
    chemicalSensingMeasured : Bool
    electricalActivityMeasured : Bool
    resourceTranslocationMeasured : Bool
    adaptiveBranchingMeasured : Bool
    memoryLikeHistoryDependenceMeasured : Bool
    perturbationRecoveryMeasured : Bool
    organismBoundarySpecified : Bool

record FungalNetworkAgencyBoundary : Set where
  field
    problemSpaceBoundary : Problem.ProblemSpaceAgencyBoundary
    autonomyBoundary : Autonomy.ConstitutiveInteractiveAutonomyBoundary
    waveBoundaryType : Set
    fungalSignallingIsBiophysical : Bool
    networkCoordinationMayBeGoalDirectedCandidate : Bool
    electricalSpikesNotNeuralLanguageByDefinition : Bool
    myceliumNotInternetOrBrainByDefinition : Bool
    forestWideWoodWebClaimsNeedSpeciesSpecificEvidence : Bool
    fungalAgencyNotHumanConsciousness : Bool
    interpretation : String

canonicalFungalNetworkAgencyBoundary : FungalNetworkAgencyBoundary
canonicalFungalNetworkAgencyBoundary = record
  { problemSpaceBoundary = Problem.canonicalProblemSpaceAgencyBoundary
  ; autonomyBoundary = Autonomy.canonicalConstitutiveInteractiveAutonomyBoundary
  ; waveBoundaryType = Wave.TravelingWaveComputationBoundary
  ; fungalSignallingIsBiophysical = true
  ; networkCoordinationMayBeGoalDirectedCandidate = true
  ; electricalSpikesNotNeuralLanguageByDefinition = true
  ; myceliumNotInternetOrBrainByDefinition = true
  ; forestWideWoodWebClaimsNeedSpeciesSpecificEvidence = true
  ; fungalAgencyNotHumanConsciousness = true
  ; interpretation = "Fungal mycelia are distributed sensing, growth and resource-allocation systems with chemical and electrical dynamics; agency-like descriptions require explicit goals and interventions, while brain, language and internet metaphors remain analogies rather than identities"
  }
