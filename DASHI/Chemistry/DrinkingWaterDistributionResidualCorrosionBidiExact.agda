module DASHI.Chemistry.DrinkingWaterDistributionResidualCorrosionBidiExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)

import DASHI.Chemistry.DrinkingWaterChlorineSpeciationExact as Free
import DASHI.Chemistry.DrinkingWaterChloramineDBPBoundaryExact as Combined
import DASHI.Chemistry.TransitionKernel as Chemistry
import DASHI.Geology.SaltGeochemistryExact as Salt

------------------------------------------------------------------------
-- DRINKING-WATER DISTRIBUTION: RESIDUAL DECAY / PIPE-WALL / CORROSION BIDI
--
-- Source anchors:
--   WHO, Principles and Practices of Drinking-water Chlorination:
--   residual chlorine can decay through reactions with bulk-water material,
--   dissolved metals, pipe materials and biofilms, with water age important.
--   WHO, Water Safety in Distribution: disinfectant, corrosion, pipe material,
--   pH and biofilm processes remain interacting but non-identical hazards.
--
-- This is a qualitative receipt layer. It does not install one universal decay
-- constant, corrosion law, pipe material, hydraulic model or regulatory limit.
------------------------------------------------------------------------

data DistributionResidualKind : Set where
  freeResidual
  combinedResidual
  : DistributionResidualKind

data PipeMaterialClass : Set where
  ironContaining
  copperContaining
  cementitious
  polymeric
  mixedOrUnknown
  : PipeMaterialClass

record DistributionHydraulicState : Set where
  constructor distributionHydraulicState
  field
    nodeOrReachReference : String
    flowReference : String
    residenceTimeReference : String
    waterAgeReference : String
    mixingReference : String
    stagnationOrDeadLegReference : String
    temperatureReference : String

open DistributionHydraulicState public

record ResidualDecayReceipt : Set₁ where
  constructor residualDecayReceipt
  field
    residualKind : DistributionResidualKind
    upstreamFreeState : Free.FreeChlorineResidualState
    hydraulicState : DistributionHydraulicState
    bulkWaterDemandReference : String
    wallDemandReference : String
    biofilmDemandReference : String
    corrosionDemandReference : String
    decayLawReference : String
    downstreamResidualMeasurementReference : String
    validationReference : String

open ResidualDecayReceipt public

record PipeWaterCorrosionInterface : Set₁ where
  constructor pipeWaterCorrosionInterface
  field
    waterChemistry : Chemistry.ReactionNetwork
    pipeMaterial : PipeMaterialClass
    chlorideSpecies : Chemistry.Species
    chlorideIsCanonical : chlorideSpecies ≡ Salt.chlorideIonSpecies
    pHReference : String
    alkalinityReference : String
    dissolvedOxygenReference : String
    conductivityIonicStrengthReference : String
    chlorideSulfateAndOtherAggressiveIonReference : String
    corrosionScaleReference : String
    metalReleaseReference : String
    pipeWallMassTransferReference : String
    empiricalCorrosionValidationReference : String

open PipeWaterCorrosionInterface public

record DistributionTapObservation : Set where
  constructor distributionTapObservation
  field
    tapLocationReference : String
    samplingTimeReference : String
    residualMeasurementReference : String
    pHMeasurementReference : String
    conductivityReference : String
    chlorideMeasurementReference : String
    metalMeasurementReference : String
    samplingProtocolReference : String

open DistributionTapObservation public

record DistributionResidualCorrosionBoundary : Set where
  constructor distributionResidualCorrosionBoundary
  field
    treatmentPlantResidualEqualsTapResidual : Bool
    treatmentPlantResidualEqualsTapResidualIsFalse : treatmentPlantResidualEqualsTapResidual ≡ false

    waterAgeAloneDeterminesResidualDecay : Bool
    waterAgeAloneDeterminesResidualDecayIsFalse : waterAgeAloneDeterminesResidualDecay ≡ false

    chloridePresenceAloneProvesCorrosionCause : Bool
    chloridePresenceAloneProvesCorrosionCauseIsFalse : chloridePresenceAloneProvesCorrosionCause ≡ false

    corrosionObservationIdentifiesUniquePipeWallMechanism : Bool
    corrosionObservationIdentifiesUniquePipeWallMechanismIsFalse :
      corrosionObservationIdentifiesUniquePipeWallMechanism ≡ false

    tapResidualRecoversTreatmentAndDistributionHistory : Bool
    tapResidualRecoversTreatmentAndDistributionHistoryIsFalse :
      tapResidualRecoversTreatmentAndDistributionHistory ≡ false

    tapChlorideIdentifiesItsGeologicalSaltSource : Bool
    tapChlorideIdentifiesItsGeologicalSaltSourceIsFalse :
      tapChlorideIdentifiesItsGeologicalSaltSource ≡ false

    distributionSafetyNeedsHydraulicChemicalMaterialAndMonitoringReceipts : Bool
    distributionSafetyNeedsHydraulicChemicalMaterialAndMonitoringReceiptsIsTrue :
      distributionSafetyNeedsHydraulicChemicalMaterialAndMonitoringReceipts ≡ true

canonicalDistributionResidualCorrosionBoundary : DistributionResidualCorrosionBoundary
canonicalDistributionResidualCorrosionBoundary =
  distributionResidualCorrosionBoundary
    false refl false refl false refl false refl false refl false refl true refl
