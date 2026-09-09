module DASHI.Environment.PlasmaActivatedWaterAquaticNutrientBridgeExact where

open import DASHI.Core.Prelude

import DASHI.Environment.AquaticLivingInfrastructureExact as Aquatic
import DASHI.Environment.QuantitiesConservation as Conservation
import DASHI.Environment.EcologicalEvidenceGates as Evidence
import DASHI.Physics.Plasma.PlasmaActivatedWaterAgricultureSourceRegistryExact as Sources

------------------------------------------------------------------------
-- PLASMA-ACTIVATED WATER -> AQUATIC / HYDROPONIC NUTRIENT BRIDGE
--
-- External literature supplies bounded plasma-liquid chemistry and agronomic
-- evidence.  The typed cross-domain bridge below is DASHI reconstruction.
--
--   plasma exposure
--      != measured composition
--      != nitrogen-input receipt
--      != complete fertiliser
--      != plant uptake
--      != crop response
--      != site recommendation.
------------------------------------------------------------------------

data PlasmaWaterProductionMode : Set where
  directLiquidExposure
  plasmaEffluentExposure
  gasPhaseDischargeOverLiquid : PlasmaWaterProductionMode

data ReactiveSpeciesCoordinate : Set where
  nitrate
  nitrite
  hydrogenPeroxide
  otherReactiveOxygenNitrogenSpecies : ReactiveSpeciesCoordinate

data ApplicationRoute : Set where
  hydroponicNutrientSolution
  aquaponicSupplement
  soilIrrigation
  seedTreatment
  foliarApplication : ApplicationRoute

record PlasmaWaterProductionIdentity : Set where
  constructor plasma-water-production-identity
  field
    mode : PlasmaWaterProductionMode
    dischargeReference : String
    feedGasReference : String
    sourceWaterReference : String
    treatmentTimeReference : String
    electricalEnergyReference : String
    reactorGeometryReference : String
    temperatureReference : String
    storageTimeReference : String
    productionSource : Sources.PAWSourceReference

open PlasmaWaterProductionIdentity public

record PlasmaActivatedWaterComposition
    (production : PlasmaWaterProductionIdentity) : Set where
  constructor plasma-activated-water-composition
  field
    pHReference : String
    conductivityReference : String
    oxidationReductionPotentialReference : String
    nitrateReference : String
    nitriteReference : String
    hydrogenPeroxideReference : String
    otherReactiveSpeciesReference : String
    analyticalMethodReference : String
    measurementUncertaintyReference : String
    measurementProvenance : Evidence.EvidenceSource

open PlasmaActivatedWaterComposition public

record PlasmaNitrogenInputReceipt
    {production : PlasmaWaterProductionIdentity}
    (composition : PlasmaActivatedWaterComposition production) : Set where
  constructor plasma-nitrogen-input-receipt
  field
    measuredNitrogenSpeciesReference : String
    nitrogenMassOrConcentrationReference : String
    applicationVolumeReference : String
    nitrogenInputToLedger : Conservation.Quantity Conservation.nitrogenGrams
    accountingModelReference : String
    compositionToLedgerWeldReference : String

open PlasmaNitrogenInputReceipt public

record PlasmaWaterApplication
    {production : PlasmaWaterProductionIdentity}
    (composition : PlasmaActivatedWaterComposition production) : Set where
  constructor plasma-water-application
  field
    route : ApplicationRoute
    targetSystemReference : String
    dilutionReference : String
    doseReference : String
    timingReference : String
    targetSpeciesOrCropReference : String
    siteOrRootZoneHistoryReference : String
    comparatorReference : String
    safetyCompatibilityReference : String

open PlasmaWaterApplication public

------------------------------------------------------------------------
-- Aquatic/hydroponic same-object weld.
------------------------------------------------------------------------

record PAWAquaticNutrientWeld
    {production : PlasmaWaterProductionIdentity}
    {composition : PlasmaActivatedWaterComposition production}
    (application : PlasmaWaterApplication composition)
    (system : Aquatic.AquaticLivingSystem) : Set where
  constructor paw-aquatic-nutrient-weld
  field
    sameWaterOrDeclaredSupplementReference : String
    nitrogenInput : PlasmaNitrogenInputReceipt composition
    receivingWaterStateReference : String
    receivingNitrogenBalance : Conservation.NitrogenBalance
    applicationIncludedInNitrogenBalanceReference : String
    pHCompatibilityReference : String
    conductivitySalinityCompatibilityReference : String
    reactiveSpeciesCompatibilityReference : String
    floraFaunaMicrobeCompatibilityReference : String
    postApplicationWaterChemistryReference : String

open PAWAquaticNutrientWeld public

------------------------------------------------------------------------
-- Agronomic outcome remains a separate evidence object.
------------------------------------------------------------------------

record PAWAgronomicOutcomeEvidence
    {production : PlasmaWaterProductionIdentity}
    {composition : PlasmaActivatedWaterComposition production}
    (application : PlasmaWaterApplication composition) : Set where
  constructor paw-agronomic-outcome-evidence
  field
    outcomeCoordinate : String
    populationOrCrop : String
    comparator : String
    measurementMethod : String
    estimateReference : String
    uncertaintyOrHeterogeneityReference : String
    source : Sources.PAWSourceReference
    transferScope : String

open PAWAgronomicOutcomeEvidence public

------------------------------------------------------------------------
-- WrongType / non-promotion barriers.
------------------------------------------------------------------------

data PlasmaContactMeansPAWCompositionPermission : Set where
data PAWMeansFertiliserPermission : Set where
data NitratePresenceMeansCompleteFertiliserPermission : Set where
data NitrogenInputMeansPlantUptakePermission : Set where
data PlantUptakeMeansGrowthBenefitPermission : Set where
data MetaAnalysisMeansAquaponicCompatibilityPermission : Set where
data PAWMeansAquacultureSafePermission : Set where
data SameNitrateMeansSamePAWPermission : Set where
data SamePAWCompositionMeansSameOutcomePermission : Set where

plasmaContactDoesNotDetermineComposition : PlasmaContactMeansPAWCompositionPermission → ⊥
plasmaContactDoesNotDetermineComposition ()

pawLabelDoesNotDefinitionallyMeanFertiliser : PAWMeansFertiliserPermission → ⊥
pawLabelDoesNotDefinitionallyMeanFertiliser ()

nitratePresenceDoesNotMakeCompleteFertiliser : NitratePresenceMeansCompleteFertiliserPermission → ⊥
nitratePresenceDoesNotMakeCompleteFertiliser ()

nitrogenInputDoesNotProvePlantUptake : NitrogenInputMeansPlantUptakePermission → ⊥
nitrogenInputDoesNotProvePlantUptake ()

plantUptakeDoesNotProveGrowthBenefit : PlantUptakeMeansGrowthBenefitPermission → ⊥
plantUptakeDoesNotProveGrowthBenefit ()

metaAnalysisDoesNotProveAquaponicCompatibility : MetaAnalysisMeansAquaponicCompatibilityPermission → ⊥
metaAnalysisDoesNotProveAquaponicCompatibility ()

pawDoesNotDefinitionallyProveAquacultureSafety : PAWMeansAquacultureSafePermission → ⊥
pawDoesNotDefinitionallyProveAquacultureSafety ()

sameNitrateDoesNotIdentifySamePAW : SameNitrateMeansSamePAWPermission → ⊥
sameNitrateDoesNotIdentifySamePAW ()

sameCompositionDoesNotDetermineSameOutcome : SamePAWCompositionMeansSameOutcomePermission → ⊥
sameCompositionDoesNotDetermineSameOutcome ()

record PlasmaActivatedWaterAquaticBoundary : Set where
  constructor plasma-activated-water-aquatic-boundary
  field
    productionAndMeasuredCompositionRemainDistinct : Bool
    nitrogenInputAndCompleteFertiliserRemainDistinct : Bool
    nitrogenInputAndBiologicalUptakeRemainDistinct : Bool
    chemicalTreatmentAndAgronomicOutcomeRemainDistinct : Bool
    plantAndAquaticCompatibilityRemainDistinct : Bool
    nitrogenMassIsExplicitlyAccounted : Bool
    sourceClaimAndDashiBridgeRemainDistinct : Bool
    plasmaTouchAutomaticallyMeansFertiliser : Bool

canonicalPlasmaActivatedWaterAquaticBoundary : PlasmaActivatedWaterAquaticBoundary
canonicalPlasmaActivatedWaterAquaticBoundary =
  plasma-activated-water-aquatic-boundary
    true true true true true true true false
