module DASHI.Environment.NitrogenPathwayEnergeticMaterialComparisonExact where

open import DASHI.Core.Prelude

import DASHI.Physics.Units.SI as SI
import DASHI.Environment.QuantitiesConservation as Conservation
import DASHI.Environment.NitrogenPathwaySourceRegistryExact as Sources
import DASHI.Environment.PlasmaActivatedWaterAquaticNutrientBridgeExact as PAW

------------------------------------------------------------------------
-- COMMON NITROGEN-PATHWAY CONSUMER FIBRE
--
-- Key correction:
--   nitrogen fixation != nitrogen transformation != nitrogen recycling
--
-- Haber-Bosch, plasma fixation and biological fixation may introduce newly
-- fixed atmospheric nitrogen into a managed boundary.  Compost mineralisation,
-- aquaponic recovery and KNF/local recycling normally transform/recover
-- previously fixed nitrogen unless an explicit fixation receipt says otherwise.
------------------------------------------------------------------------

data NitrogenOrigin : Set where
  newlyFixedAtmosphericNitrogen
  recycledPreviouslyFixedNitrogen
  mixedOrOriginUnresolved : NitrogenOrigin

data NitrogenPathway : Set where
  haberBoschDerivedNitrogen
  plasmaFixedNitrogen
  biologicalNitrogenFixation
  compostMineralisation
  aquaponicWasteRecovery
  knfLocalRecycling : NitrogenPathway

data NitrogenDeliveryRoute : Set where
  manufacturedFertiliserInput
  aqueousNutrientInput
  symbioticRootFixation
  soilOrganicAmendment
  recirculatingAquaticNutrient
  localMaterialRecycling : NitrogenDeliveryRoute

originForPathway : NitrogenPathway → NitrogenOrigin
originForPathway haberBoschDerivedNitrogen = newlyFixedAtmosphericNitrogen
originForPathway plasmaFixedNitrogen = newlyFixedAtmosphericNitrogen
originForPathway biologicalNitrogenFixation = newlyFixedAtmosphericNitrogen
originForPathway compostMineralisation = recycledPreviouslyFixedNitrogen
originForPathway aquaponicWasteRecovery = recycledPreviouslyFixedNitrogen
originForPathway knfLocalRecycling = recycledPreviouslyFixedNitrogen

sourceForPathway : NitrogenPathway → Sources.NitrogenPathwaySource
sourceForPathway haberBoschDerivedNitrogen = Sources.haberBoschReview2024
sourceForPathway plasmaFixedNitrogen = Sources.plasmaNitrogenSource
sourceForPathway biologicalNitrogenFixation = Sources.hungriaBNFSource
sourceForPathway compostMineralisation = Sources.compostNitrogenReview2003
sourceForPathway aquaponicWasteRecovery = Sources.aquaponicNitrogenRecoverySource
sourceForPathway knfLocalRecycling = Sources.knfLocalRecyclingLineage

record PlantAvailableNitrogenReceipt : Set where
  constructor plant-available-nitrogen-receipt
  field
    totalNitrogen : Conservation.Quantity Conservation.nitrogenGrams
    plantAvailableNitrogen : Conservation.Quantity Conservation.nitrogenGrams
    availabilityDoesNotExceedTotal :
      Conservation.quantityMonotone plantAvailableNitrogen totalNitrogen
    availabilityModelReference : String
    measurementOrTransformationReference : String
    timeHorizonReference : String

open PlantAvailableNitrogenReceipt public

record NitrogenDeliveryPacket : Set where
  constructor nitrogen-delivery-packet
  field
    pathway : NitrogenPathway
    origin : NitrogenOrigin
    originMatchesPathway : origin ≡ originForPathway pathway
    deliveryRoute : NitrogenDeliveryRoute
    nitrogen : PlantAvailableNitrogenReceipt
    externalEnergy : SI.Quantity SI.Energy SI.unitScale
    energyBoundaryReference : String
    waterUse : Conservation.Quantity Conservation.waterLitres
    emissions : Conservation.Quantity Conservation.emissionGramsCO2e
    emissionsBoundaryReference : String
    nitrogenBalance : Conservation.NitrogenBalance
    systemBoundaryReference : String
    siteHistoryReference : String
    source : Sources.NitrogenPathwaySource
    sourceMatchesPathway : source ≡ sourceForPathway pathway

open NitrogenDeliveryPacket public

------------------------------------------------------------------------
-- PAW adapter: measured PAW nitrogen can enter the common consumer fibre,
-- but plant availability, energy boundary and lifecycle fields remain inputs.
------------------------------------------------------------------------

record PAWComparisonAdapter
    {production : PAW.PlasmaWaterProductionIdentity}
    {composition : PAW.PlasmaActivatedWaterComposition production}
    (pawNitrogen : PAW.PlasmaNitrogenInputReceipt composition) : Set where
  constructor paw-comparison-adapter
  field
    availability : PlantAvailableNitrogenReceipt
    totalNitrogenMatchesPAWLedger :
      totalNitrogen availability ≡ PAW.nitrogenInputToLedger pawNitrogen
    externalEnergy : SI.Quantity SI.Energy SI.unitScale
    energyMeasurementReference : String
    waterUse : Conservation.Quantity Conservation.waterLitres
    emissions : Conservation.Quantity Conservation.emissionGramsCO2e
    emissionsBoundaryReference : String
    nitrogenBalance : Conservation.NitrogenBalance
    systemBoundaryReference : String
    siteHistoryReference : String

open PAWComparisonAdapter public

compilePAWPacket :
  {production : PAW.PlasmaWaterProductionIdentity} →
  {composition : PAW.PlasmaActivatedWaterComposition production} →
  (pawNitrogen : PAW.PlasmaNitrogenInputReceipt composition) →
  PAWComparisonAdapter pawNitrogen →
  NitrogenDeliveryPacket
compilePAWPacket pawNitrogen adapter =
  nitrogen-delivery-packet
    plasmaFixedNitrogen
    newlyFixedAtmosphericNitrogen
    refl
    aqueousNutrientInput
    (PAWComparisonAdapter.availability adapter)
    (PAWComparisonAdapter.externalEnergy adapter)
    (PAWComparisonAdapter.energyMeasurementReference adapter)
    (PAWComparisonAdapter.waterUse adapter)
    (PAWComparisonAdapter.emissions adapter)
    (PAWComparisonAdapter.emissionsBoundaryReference adapter)
    (PAWComparisonAdapter.nitrogenBalance adapter)
    (PAWComparisonAdapter.systemBoundaryReference adapter)
    (PAWComparisonAdapter.siteHistoryReference adapter)
    Sources.plasmaNitrogenSource
    refl

------------------------------------------------------------------------
-- Fair comparison requires a shared consumer boundary; equal delivered N does
-- not erase mechanism, origin, energy, water, emissions or provenance.
------------------------------------------------------------------------

record NitrogenPathwayComparison : Set where
  constructor nitrogen-pathway-comparison
  field
    left : NitrogenDeliveryPacket
    right : NitrogenDeliveryPacket
    samePlantAvailableNitrogenConsumerReference : String
    sameSystemBoundaryReference : String
    sameTimeHorizonReference : String
    sameOutcomeDefinitionReference : String
    energyAccountingComparableReference : String
    emissionsAccountingComparableReference : String
    waterAccountingComparableReference : String
    uncertaintyReference : String

open NitrogenPathwayComparison public

------------------------------------------------------------------------
-- WrongType / anti-flattening barriers.
------------------------------------------------------------------------

data TotalNitrogenMeansPlantAvailablePermission : Set where
data PlantAvailableMeansPlantUptakePermission : Set where
data SameDeliveredNitrogenMeansSameEnergyPermission : Set where
data SameDeliveredNitrogenMeansSameEmissionsPermission : Set where
data SameDeliveredNitrogenMeansSameProvenancePermission : Set where
data RecycledNitrogenMeansNewFixationPermission : Set where
data InoculantMeansFixationReceiptPermission : Set where
data CompostTotalNitrogenMeansImmediateAvailabilityPermission : Set where
data AquacultureWasteMeansPlantAvailableNitrogenPermission : Set where
data KNFRecyclingMeansAtmosphericFixationPermission : Set where
data AmmoniaMeansCompleteFertiliserPermission : Set where
data LowestEnergyMeansBestRecommendationPermission : Set where

totalNitrogenDoesNotDeterminePlantAvailability : TotalNitrogenMeansPlantAvailablePermission → ⊥
totalNitrogenDoesNotDeterminePlantAvailability ()

plantAvailableNitrogenDoesNotProveUptake : PlantAvailableMeansPlantUptakePermission → ⊥
plantAvailableNitrogenDoesNotProveUptake ()

sameNitrogenDoesNotDetermineEnergy : SameDeliveredNitrogenMeansSameEnergyPermission → ⊥
sameNitrogenDoesNotDetermineEnergy ()

sameNitrogenDoesNotDetermineEmissions : SameDeliveredNitrogenMeansSameEmissionsPermission → ⊥
sameNitrogenDoesNotDetermineEmissions ()

sameNitrogenDoesNotEraseProvenance : SameDeliveredNitrogenMeansSameProvenancePermission → ⊥
sameNitrogenDoesNotEraseProvenance ()

recyclingDoesNotDefinitionallyFixNewNitrogen : RecycledNitrogenMeansNewFixationPermission → ⊥
recyclingDoesNotDefinitionallyFixNewNitrogen ()

inoculantPresenceDoesNotProveFixation : InoculantMeansFixationReceiptPermission → ⊥
inoculantPresenceDoesNotProveFixation ()

compostTotalNitrogenDoesNotMeanImmediateAvailability : CompostTotalNitrogenMeansImmediateAvailabilityPermission → ⊥
compostTotalNitrogenDoesNotMeanImmediateAvailability ()

aquacultureWasteDoesNotDefinitionallyMeanPlantAvailableNitrogen : AquacultureWasteMeansPlantAvailableNitrogenPermission → ⊥
aquacultureWasteDoesNotDefinitionallyMeanPlantAvailableNitrogen ()

knfRecyclingDoesNotDefinitionallyFixAtmosphericNitrogen : KNFRecyclingMeansAtmosphericFixationPermission → ⊥
knfRecyclingDoesNotDefinitionallyFixAtmosphericNitrogen ()

ammoniaDoesNotDefinitionallyMeanCompleteFertiliser : AmmoniaMeansCompleteFertiliserPermission → ⊥
ammoniaDoesNotDefinitionallyMeanCompleteFertiliser ()

lowestEnergyDoesNotAutomaticallyPromoteRecommendation : LowestEnergyMeansBestRecommendationPermission → ⊥
lowestEnergyDoesNotAutomaticallyPromoteRecommendation ()

record NitrogenComparisonBoundary : Set where
  constructor nitrogen-comparison-boundary
  field
    fixationTransformationAndRecyclingRemainDistinct : Bool
    totalAndPlantAvailableNitrogenRemainDistinct : Bool
    nitrogenEnergyWaterEmissionsRemainDistinctLedgers : Bool
    sameConsumerCoordinateDoesNotEraseMechanism : Bool
    sameConsumerCoordinateDoesNotEraseSourceProvenance : Bool
    sourceClaimAndDashiComparisonRemainDistinct : Bool
    comparisonAutomaticallySelectsBestPractice : Bool

canonicalNitrogenComparisonBoundary : NitrogenComparisonBoundary
canonicalNitrogenComparisonBoundary =
  nitrogen-comparison-boundary true true true true true true false
