module DASHI.Chemistry.OceanCarbonateSaltTemperatureStressBidiExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)

import DASHI.Geology.SaltGeochemistryExact as Salt
import DASHI.Chemistry.DrinkingWaterChlorineSpeciationExact as Speciation
import DASHI.Core.ConsumerRelativeCoarseGrainingBidiExact as Coarse
import DASHI.Core.ActiveBidiDiscriminatorLoopExact as Bidi

------------------------------------------------------------------------
-- OCEAN CARBONATE / SALINITY / TEMPERATURE MULTI-STRESSOR BIDI
--
-- Bounded empirical calibration:
-- NOAA: atmospheric CO2 uptake increases dissolved CO2, hydrogen ion activity,
-- lowers pH and carbonate-ion availability; pH, pCO2, total alkalinity and DIC
-- are distinct observation coordinates. Ocean warming, circulation, local
-- biogeochemistry and other stressors interact with carbonate chemistry.
--
-- Salinity is retained as an independent physical/ionic coordinate: a bulk
-- salinity scalar does not recover carbonate speciation, alkalinity, nutrient
-- state, temperature or ecological response.
------------------------------------------------------------------------

data OceanStressCoordinate : Set where
  temperature
  salinity
  dissolvedCO2
  pH
  totalAlkalinity
  dissolvedInorganicCarbon
  carbonateIonAvailability
  oxygenState
  nutrientState
  : OceanStressCoordinate

data EcologicalResponseCoordinate : Set where
  calcificationCapacity
  metabolicTolerance
  reproductiveSuccess
  habitatSuitability
  foodWebSupport
  populationPersistence
  : EcologicalResponseCoordinate

record OceanCarbonateObservationReceipt : Set where
  constructor ocean-carbonate-observation-receipt
  field
    locationTimeReference : String
    temperatureReference : String
    salinityReference : String
    pHReference : String
    pCO2Reference : String
    alkalinityReference : String
    DICReference : String
    carbonateSaturationReference : String
    oxygenReference : String
    nutrientReference : String
    methodCalibrationReference : String
    provenanceReference : String

record MultiStressEcologyReceipt : Set where
  constructor multi-stress-ecology-receipt
  field
    speciesCommunityReference : String
    exposureHistoryReference : String
    temperatureResponseReference : String
    salinityResponseReference : String
    carbonateChemistryResponseReference : String
    oxygenResponseReference : String
    interactionReference : String
    acclimationAdaptationReference : String
    ecologicalValidationReference : String

saltBoundary : Salt.SaltGeochemistryBoundary
saltBoundary = Salt.canonicalSaltGeochemistryBoundary

coarseBoundary : Coarse.ConsumerRelativeCoarseGrainingBoundary
coarseBoundary = Coarse.canonicalConsumerRelativeCoarseGrainingBoundary

activeBidiBoundary : Bidi.ActiveBidiDiscriminatorLoopBoundary
activeBidiBoundary = Bidi.canonicalActiveBidiDiscriminatorLoopBoundary

record OceanCarbonateSaltTemperatureStressBoundary : Set where
  constructor ocean-carbonate-salt-temperature-stress-boundary
  field
    salinityScalarDeterminesCarbonateChemistry : Bool
    salinityScalarDeterminesCarbonateChemistryIsFalse :
      salinityScalarDeterminesCarbonateChemistry ≡ false
    pHAloneDeterminesFullCarbonateSystem : Bool
    pHAloneDeterminesFullCarbonateSystemIsFalse :
      pHAloneDeterminesFullCarbonateSystem ≡ false
    warmingEqualsAcidification : Bool
    warmingEqualsAcidificationIsFalse : warmingEqualsAcidification ≡ false
    oceanCO2UptakeCanAlterCarbonateChemistry : Bool
    oceanCO2UptakeCanAlterCarbonateChemistryIsTrue :
      oceanCO2UptakeCanAlterCarbonateChemistry ≡ true
    lowerPHAutomaticallyDeterminesOneEcologicalOutcome : Bool
    lowerPHAutomaticallyDeterminesOneEcologicalOutcomeIsFalse :
      lowerPHAutomaticallyDeterminesOneEcologicalOutcome ≡ false
    ecologicalAssessmentNeedsMultiCoordinateStressHistory : Bool
    ecologicalAssessmentNeedsMultiCoordinateStressHistoryIsTrue :
      ecologicalAssessmentNeedsMultiCoordinateStressHistory ≡ true
    coarseOceanIndexCanBeAdequateForOneConsumerButNotAnother : Bool
    coarseOceanIndexCanBeAdequateForOneConsumerButNotAnotherIsTrue :
      coarseOceanIndexCanBeAdequateForOneConsumerButNotAnother ≡ true
    reading : String

canonicalOceanCarbonateSaltTemperatureStressBoundary :
  OceanCarbonateSaltTemperatureStressBoundary
canonicalOceanCarbonateSaltTemperatureStressBoundary =
  ocean-carbonate-salt-temperature-stress-boundary
    false refl
    false refl
    false refl
    true refl
    false refl
    true refl
    true refl
    "Ocean climate stress is multiaxial: temperature, salinity, CO2/carbonate chemistry, oxygen, nutrients and biological history are distinct coordinates. Atmospheric-carbon uptake can change pH and carbonate availability, but neither salinity nor pH alone recovers the full chemical or ecological fibre."
