module DASHI.Biology.Levin.SubstrateConstrainedComputation where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)

import DASHI.Biology.Levin.SubstrateIndependentAgency as Agency
import DASHI.Biology.Levin.TravelingWaveComputationBoundary as Wave
import DASHI.Biology.Levin.BioelectricChemistryWaveAdapter as Chemistry

------------------------------------------------------------------------
-- Computation is compared extensionally only after the physically
-- available state transitions, timescales, coupling laws and embodiment
-- constraints have been declared.

record PhysicalComputationCarrier : Set where
  field
    continuousStateAvailable      : Bool
    discreteThresholdsAvailable   : Bool
    multiscaleCouplingAvailable   : Bool
    parallelInteractionAvailable  : Bool
    fieldDynamicsAvailable        : Bool
    morphologyConstrainsDynamics  : Bool
    energeticBudgetExplicit       : Bool
    temporalResolutionExplicit    : Bool

record SubstrateConstrainedComputationBoundary : Set where
  field
    agencyBoundary        : Agency.SubstrateIndependentAgencyBoundary
    waveBoundaryType      : Set
    chemistryBoundary     : Chemistry.BioelectricChemistryWaveAdapter
    sameInputOutputDoesNotFixInternalComputation : Bool
    analogNotSufficientForConsciousness          : Bool
    digitalNotAbsenceOfUnderlyingContinuity      : Bool
    biologicalSubstrateNotUniquelyRequired       : Bool
    substrateNeverIrrelevant                     : Bool
    consciousnessRequiresSeparateWitness         : Bool
    interpretation : String

canonicalPhysicalComputationCarrier : PhysicalComputationCarrier
canonicalPhysicalComputationCarrier = record
  { continuousStateAvailable = true
  ; discreteThresholdsAvailable = true
  ; multiscaleCouplingAvailable = true
  ; parallelInteractionAvailable = true
  ; fieldDynamicsAvailable = true
  ; morphologyConstrainsDynamics = true
  ; energeticBudgetExplicit = true
  ; temporalResolutionExplicit = true
  }

canonicalSubstrateConstrainedComputationBoundary :
  SubstrateConstrainedComputationBoundary
canonicalSubstrateConstrainedComputationBoundary = record
  { agencyBoundary = Agency.canonicalSubstrateIndependentAgencyBoundary
  ; waveBoundaryType = Wave.TravelingWaveComputationBoundary
  ; chemistryBoundary = Chemistry.canonicalBioelectricChemistryWaveAdapter
  ; sameInputOutputDoesNotFixInternalComputation = true
  ; analogNotSufficientForConsciousness = true
  ; digitalNotAbsenceOfUnderlyingContinuity = true
  ; biologicalSubstrateNotUniquelyRequired = true
  ; substrateNeverIrrelevant = true
  ; consciousnessRequiresSeparateWitness = true
  ; interpretation = "Extensional behaviour underdetermines the physically realised computation; substrate constrains admissible state transitions without making biology uniquely sufficient or necessary for consciousness"
  }
