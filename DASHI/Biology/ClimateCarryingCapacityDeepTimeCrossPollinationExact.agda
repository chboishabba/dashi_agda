module DASHI.Biology.ClimateCarryingCapacityDeepTimeCrossPollinationExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)

import DASHI.Biology.NaturalSystemsHyperfabricExact as Natural
import DASHI.Biology.DeepTimeCarbonBiosphereFossilFuelBidiExact as DeepTime
import DASHI.Chemistry.OceanCarbonateSaltTemperatureStressBidiExact as Ocean
import DASHI.Chemistry.SaltPetroleumIndustrialChemistryNetworkExact as Industry
import DASHI.Core.HistoryConditionedChoiceExact as History
import DASHI.Core.ActiveBidiDiscriminatorLoopExact as Bidi

------------------------------------------------------------------------
-- CLIMATE / ECOLOGICAL CARRYING-CAPACITY / DEEP-TIME CROSS-POLLINATION
--
-- Carrying capacity is treated as environment-, species/community-, resource-
-- and history-indexed.  A single global scalar is not installed as an ecology
-- theorem.  The Carboniferous appears as a deep-time comparison regime in which
-- biosphere, climate, atmospheric composition, wetlands and carbon burial were
-- materially different from the present.
------------------------------------------------------------------------

data ClimateEcologyCoordinate : Set where
  temperatureRegime
  precipitationHydrology
  atmosphericCO2
  oceanPH
  oceanSalinity
  oxygenAvailability
  nutrientAvailability
  habitatArea
  trophicSupport
  disturbanceRegime
  : ClimateEcologyCoordinate

data DeepTimeComparisonRegime : Set where
  carboniferousWetlandCoalWorld
  mesozoicFaunalWorld
  preindustrialHolocene
  industrialAnthropocene
  : DeepTimeComparisonRegime

record CarryingCapacityContext : Set where
  constructor carrying-capacity-context
  field
    speciesCommunityReference : String
    spatialScaleReference : String
    temporalScaleReference : String
    resourceReference : String
    temperatureReference : String
    salinityHydrologyReference : String
    carbonateChemistryReference : String
    oxygenNutrientReference : String
    habitatReference : String
    competitionPredationReference : String
    disturbanceReference : String
    historicalAdaptationReference : String
    validationReference : String

record DeepTimeClimateComparisonReceipt : Set where
  constructor deep-time-climate-comparison-receipt
  field
    earlierRegime : DeepTimeComparisonRegime
    laterRegime : DeepTimeComparisonRegime
    atmosphericReference : String
    oceanReference : String
    vegetationEcosystemReference : String
    carbonBurialReference : String
    biodiversityReference : String
    geologicalProxyReference : String
    uncertaintyReference : String
    validationReference : String

naturalBoundary : Natural.NaturalSystemsBoundary
naturalBoundary = Natural.canonicalNaturalSystemsBoundary

deepTimeBoundary : DeepTime.DeepTimeCarbonBiosphereFossilFuelBoundary
deepTimeBoundary = DeepTime.canonicalDeepTimeCarbonBiosphereFossilFuelBoundary

oceanBoundary : Ocean.OceanCarbonateSaltTemperatureStressBoundary
oceanBoundary = Ocean.canonicalOceanCarbonateSaltTemperatureStressBoundary

industryBoundary : Industry.SaltPetroleumIndustrialChemistryBoundary
industryBoundary = Industry.canonicalSaltPetroleumIndustrialChemistryBoundary

historyBoundary : History.HistoryConditionedChoiceBoundary
historyBoundary = History.canonicalHistoryConditionedChoiceBoundary

activeBidiBoundary : Bidi.ActiveBidiDiscriminatorLoopBoundary
activeBidiBoundary = Bidi.canonicalActiveBidiDiscriminatorLoopBoundary

record ClimateCarryingCapacityDeepTimeBoundary : Set where
  constructor climate-carrying-capacity-deep-time-boundary
  field
    carryingCapacityIsTimelessSpeciesConstant : Bool
    carryingCapacityIsTimelessSpeciesConstantIsFalse :
      carryingCapacityIsTimelessSpeciesConstant ≡ false
    temperatureAloneDeterminesCarryingCapacity : Bool
    temperatureAloneDeterminesCarryingCapacityIsFalse :
      temperatureAloneDeterminesCarryingCapacity ≡ false
    presentClimateStressRecoversUniqueDeepTimeAnalogue : Bool
    presentClimateStressRecoversUniqueDeepTimeAnalogueIsFalse :
      presentClimateStressRecoversUniqueDeepTimeAnalogue ≡ false
    carboniferousComparisonCanExposeCarbonBurialEcosystemCoupling : Bool
    carboniferousComparisonCanExposeCarbonBurialEcosystemCouplingIsTrue :
      carboniferousComparisonCanExposeCarbonBurialEcosystemCoupling ≡ true
    fossilFuelIndustrialUseReconnectsDeepTimeCarbonToPresentEcology : Bool
    fossilFuelIndustrialUseReconnectsDeepTimeCarbonToPresentEcologyIsTrue :
      fossilFuelIndustrialUseReconnectsDeepTimeCarbonToPresentEcology ≡ true
    samePresentTemperatureNeedNotMeanSameEcologicalFuture : Bool
    samePresentTemperatureNeedNotMeanSameEcologicalFutureIsTrue :
      samePresentTemperatureNeedNotMeanSameEcologicalFuture ≡ true
    carryingCapacityAssessmentNeedsMultiStressAndHistoryReceipt : Bool
    carryingCapacityAssessmentNeedsMultiStressAndHistoryReceiptIsTrue :
      carryingCapacityAssessmentNeedsMultiStressAndHistoryReceipt ≡ true
    reading : String

canonicalClimateCarryingCapacityDeepTimeBoundary :
  ClimateCarryingCapacityDeepTimeBoundary
canonicalClimateCarryingCapacityDeepTimeBoundary =
  climate-carrying-capacity-deep-time-boundary
    false refl
    false refl
    false refl
    true refl
    true refl
    true refl
    true refl
    "Ecological carrying capacity is a situated future-cone property, not a timeless scalar attached to a species. Deep-time comparisons such as Carboniferous wetland/coal systems can illuminate biosphere-carbon-climate coupling, while present warming, acidification, salinity/hydrology, oxygen, nutrients and disturbance jointly alter ecological option cones. Historical analogy does not erase regime differences."
