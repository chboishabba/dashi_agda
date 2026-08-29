module DASHI.Environment.SoilPlantAtmosphereContinuumExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Environment.PlantHydraulicAtmosphereCarbonCouplingExact as Plant
import DASHI.Environment.RootSoilFungalIonWaterPhysiologyExact as RootSoil
import DASHI.Environment.SoilBiogeochemistryProcessNetworkExact as SoilBio
import DASHI.Environment.QuantitiesConservation as Conservation
import DASHI.Environment.LESDomainBasisBidiFrontierExact as Basis
import DASHI.Physics.Units.SI as SI

------------------------------------------------------------------------
-- PRIMARY SOURCE
--
-- John S. Sperry, Volker Stiller and Uwe G. Hacke,
-- "Xylem Hydraulics and the Soil-Plant-Atmosphere Continuum: Opportunities
-- and Unresolved Issues", Agronomy Journal 95(6) (2003), 1362--1370.
-- DOI: 10.2134/agronj2003.1362.
--
-- SOURCE BOUNDARY
-- The source motivates mechanistic linking of soil hydraulic availability,
-- xylem hydraulic vulnerability, stomatal regulation and canopy water use in
-- the soil-plant-atmosphere continuum. The exact dependent-state composition,
-- conservation receipts and Stage-7 carrier below are DASHI reconstruction.
------------------------------------------------------------------------

record SoilHydraulicBoundaryReceipt : Set₁ where
  constructor soilHydraulicBoundaryReceipt
  field
    SoilHydraulicState : Set
    pressureScale : SI.DecimalScale
    fluxScale : SI.DecimalScale

    soilWaterPotential : SoilHydraulicState → SI.Quantity SI.Pressure pressureScale
    soilWaterFluxDensity : SoilHydraulicState → SI.Quantity SI.Velocity fluxScale

    unsaturatedConductivityReference : String
    retentionOrStorageReference : String
    soilRootContactReference : String
    geometryReference : String
    initialBoundaryConditionReference : String
    parameterAuthorityReference : String
    validationReference : String

open SoilHydraulicBoundaryReceipt public

record SoilPlantAtmosphereContinuum
    (soil : SoilHydraulicBoundaryReceipt)
    (plant : Plant.PlantHydraulicCarbonDomainRealization) : Set₁ where
  constructor soilPlantAtmosphereContinuum
  field
    SPACState : Set

    soilState : SPACState → SoilHydraulicState soil
    plantState :
      SPACState →
      Plant.WholePlantState (Plant.wholePlant plant)

    rootSoilWaterState :
      SPACState →
      RootSoil.RootWaterState
        (RootSoil.waterTransport (Plant.rootSoilMechanism plant))

    soilPotentialToRootBoundaryReference : String
    soilFluxToRootUptakeReference : String
    rootToXylemContinuityReference : String
    xylemToLeafContinuityReference : String
    leafToAtmosphereTranspirationReference : String
    hydraulicVulnerabilityReference : String
    stomatalHydraulicFeedbackReference : String
    storageAndCapacitanceReference : String
    commonGeometryReference : String
    commonTimeReference : String
    validationReference : String

open SoilPlantAtmosphereContinuum public

------------------------------------------------------------------------
-- The same SPAC state can also consume the soil biogeochemistry network.
-- This keeps water limitation, nutrient availability and carbon allocation on
-- one explicit interaction surface without asserting a universal model.
------------------------------------------------------------------------

record SPACBiogeochemistryFeedbackWeld
    {soilHydraulics : SoilHydraulicBoundaryReceipt}
    {plant : Plant.PlantHydraulicCarbonDomainRealization}
    (spac : SoilPlantAtmosphereContinuum soilHydraulics plant)
    (soilBio : SoilBio.SoilCNProcessNetwork) : Set where
  constructor spacBiogeochemistryFeedbackWeld
  field
    soilMoistureToBiogeochemistryReference : String
    rootUptakeToMineralNReference : String
    plantCarbonAllocationToSoilReference : String
    microbialRespirationToCarbonBalanceReference : String
    transpirationToWaterBalanceReference : String
    nutrientStatusToPhotosynthesisReference : String
    waterStressToPhotosynthesisReference : String
    commonSpatialScaleReference : String
    commonTemporalScaleReference : String
    crossDomainConservationReference : String
    validationReference : String

open SPACBiogeochemistryFeedbackWeld public

record SPACDomainRealization : Set₁ where
  constructor spacDomainRealization
  field
    domainMechanism : Basis.DomainMechanismSocket
    soilHydraulics : SoilHydraulicBoundaryReceipt
    plant : Plant.PlantHydraulicCarbonDomainRealization
    continuum : SoilPlantAtmosphereContinuum soilHydraulics plant
    soilBiogeochemistry : SoilBio.SoilCNProcessNetwork
    biogeochemistryFeedback :
      SPACBiogeochemistryFeedbackWeld continuum soilBiogeochemistry
    conservation : Conservation.ConservationBundle

    stateIdentificationReference : String
    controlIdentificationReference : String
    observationIdentificationReference : String
    discrepancyModelReference : String
    experimentDesignReference : String
    identifiabilityReference : String
    heldOutValidationReference : String

open SPACDomainRealization public

sperryStillerHackeDOI : String
sperryStillerHackeDOI = "10.2134/agronj2003.1362"

record SPACBoundary : Set where
  constructor spacBoundary
  field
    sharedPressureDimensionProvesHydraulicContinuity : Bool
    sharedPressureDimensionProvesHydraulicContinuityIsFalse :
      sharedPressureDimensionProvesHydraulicContinuity ≡ false

    soilConductivityCurveIsXylemVulnerabilityCurve : Bool
    soilConductivityCurveIsXylemVulnerabilityCurveIsFalse :
      soilConductivityCurveIsXylemVulnerabilityCurve ≡ false

    steadyStateRootUptakeEqualsLeafTranspirationWithoutStorage : Bool
    steadyStateRootUptakeEqualsLeafTranspirationWithoutStorageIsFalse :
      steadyStateRootUptakeEqualsLeafTranspirationWithoutStorage ≡ false

    soilWaterAvailabilityAloneDeterminesCanopyCarbonGain : Bool
    soilWaterAvailabilityAloneDeterminesCanopyCarbonGainIsFalse :
      soilWaterAvailabilityAloneDeterminesCanopyCarbonGain ≡ false

    addingSoilBiogeochemistryAutomaticallyClosesPlantNutrition : Bool
    addingSoilBiogeochemistryAutomaticallyClosesPlantNutritionIsFalse :
      addingSoilBiogeochemistryAutomaticallyClosesPlantNutrition ≡ false

    spacRequiresLiteralCrossCompartmentReceipts : Bool
    spacRequiresLiteralCrossCompartmentReceiptsIsTrue :
      spacRequiresLiteralCrossCompartmentReceipts ≡ true

    stage7ValidationStillRequired : Bool
    stage7ValidationStillRequiredIsTrue :
      stage7ValidationStillRequired ≡ true

canonicalSPACBoundary : SPACBoundary
canonicalSPACBoundary =
  spacBoundary
    false refl
    false refl
    false refl
    false refl
    false refl
    true refl
    true refl
