module DASHI.Environment.PlantHydraulicAtmosphereCarbonCouplingExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Environment.FunctionalEcology as Ecology
import DASHI.Environment.LESFluidPhysicsCouplingExact as Fluid
import DASHI.Environment.QuantitiesConservation as Conservation
import DASHI.Environment.RootSoilFungalIonWaterPhysiologyExact as RootSoil
import DASHI.Environment.LESDomainBasisBidiFrontierExact as Basis
import DASHI.Physics.Units.SI as SI

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- Melvin T. Tyree and Martin H. Zimmermann,
-- Xylem Structure and the Ascent of Sap, 2nd ed., Springer, 2002.
-- DOI: 10.1007/978-3-662-04931-0.
--
-- G. D. Farquhar, S. von Caemmerer and J. A. Berry,
-- "A biochemical model of photosynthetic CO2 assimilation in leaves of C3
-- species", Planta 149 (1980), 78--90.
-- DOI: 10.1007/BF00386231.
--
-- Thomas N. Buckley, Lawren Sack and Graham D. Farquhar,
-- "Optimal plant water economy", Plant, Cell & Environment 40 (2017),
-- 881--896.
-- DOI: 10.1111/pce.12823.
--
-- SOURCE BOUNDARY
-- Tyree/Zimmermann motivate cohesion-tension, hydraulic architecture, xylem
-- transport and hydraulic limitation of transpiration/gas exchange. Farquhar,
-- von Caemmerer and Berry provide the C3 biochemical photosynthesis model.
-- Buckley/Sack/Farquhar review the coupling of carbon gain and water loss via
-- stomatal regulation and plant water economy.
--
-- The exact SI-typed sockets, same-state welds, atmosphere/fluid adapters and
-- Stage-7 interfaces below are DASHI reconstruction. No universal hydraulic,
-- stomatal, photosynthetic, vulnerability or growth parameterisation is
-- attributed to these sources.
------------------------------------------------------------------------

data XylemTransportRegime : Set where
  cohesionTensionXylem
  applicationSpecificHydraulicReduction
  : XylemTransportRegime

record XylemHydraulicReceipt
    (root : RootSoil.RootSoilIonWaterMechanism) : Set₁ where
  constructor xylemHydraulicReceipt
  field
    XylemState : Set
    pressureScale : SI.DecimalScale
    axialFluxScale : SI.DecimalScale

    rootXylemWaterPotential : XylemState → SI.Quantity SI.Pressure pressureScale
    leafXylemWaterPotential : XylemState → SI.Quantity SI.Pressure pressureScale
    axialWaterFluxDensity : XylemState → SI.Quantity SI.Velocity axialFluxScale

    regime : XylemTransportRegime
    fluidReduction : Fluid.FluidReductionReceipt
    rootWaterSourceIdentificationReference : String
    xylemGeometryReference : String
    hydraulicConductanceReference : String
    gravityAndPressureDrivingReference : String
    capacitanceOrStorageReference : String
    embolismVulnerabilityReference : String
    initialBoundaryConditionReference : String
    validationReference : String

open XylemHydraulicReceipt public

------------------------------------------------------------------------
-- Atmosphere-facing leaf gas exchange.
--
-- Carbon assimilation and transpiration are both molar flux densities, but
-- they are not the same transported substance. Keeping separate projections is
-- therefore stronger than relying on a shared SI dimension alone.
------------------------------------------------------------------------

record LeafGasExchangeReceipt : Set₁ where
  constructor leafGasExchangeReceipt
  field
    LeafState : Set
    AtmosphereState : Set

    pressureScale : SI.DecimalScale
    temperatureScale : SI.DecimalScale
    gasFluxScale : SI.DecimalScale

    leafWaterPotential : LeafState → SI.Quantity SI.Pressure pressureScale
    vapourPressureDeficit : AtmosphereState → SI.Quantity SI.Pressure pressureScale
    leafTemperature : LeafState → SI.Quantity SI.Temperature temperatureScale

    transpirationFlux :
      LeafState → AtmosphereState → SI.Quantity SI.MolarFluxDensity gasFluxScale
    carbonAssimilationFlux :
      LeafState → AtmosphereState → SI.Quantity SI.MolarFluxDensity gasFluxScale

    farquharC3ModelReference : String
    stomatalConductanceReference : String
    carbonWaterEconomyReference : String
    boundaryLayerReference : String
    atmosphericCO2Reference : String
    humidityReference : String
    illuminationReference : String
    photosyntheticParameterAuthorityReference : String
    validationReference : String

open LeafGasExchangeReceipt public

------------------------------------------------------------------------
-- Wind / atmospheric transport remains an explicit fluid application receipt.
------------------------------------------------------------------------

record LeafAtmosphereFluidWeld
    (leaf : LeafGasExchangeReceipt) : Set₁ where
  constructor leafAtmosphereFluidWeld
  field
    atmosphericFluid : Fluid.FluidReductionReceipt
    atmosphericApplicationIsWind :
      Fluid.application atmosphericFluid ≡ Fluid.atmosphericWind

    AtmosphereCoupledState : Set
    gasExchangeAtmosphereState : AtmosphereCoupledState → AtmosphereState leaf
    fluidAtmosphereState :
      AtmosphereCoupledState → Fluid.FluidState (Fluid.fieldSocket atmosphericFluid)

    windBoundaryLayerIdentificationReference : String
    temperatureHumidityCoLocationReference : String
    commonTimeSupportReference : String
    atmosphereValidationReference : String

open LeafAtmosphereFluidWeld public

------------------------------------------------------------------------
-- Whole-plant same-state weld.
------------------------------------------------------------------------

record WholePlantHydraulicCarbonWeld
    (root : RootSoil.RootSoilIonWaterMechanism)
    (xylem : XylemHydraulicReceipt root)
    (leaf : LeafGasExchangeReceipt)
    (atmosphere : LeafAtmosphereFluidWeld leaf) : Set₁ where
  constructor wholePlantHydraulicCarbonWeld
  field
    WholePlantState : Set

    rootWaterState :
      WholePlantState →
      RootSoil.RootWaterState (RootSoil.waterTransport root)
    xylemState : WholePlantState → XylemState xylem
    leafState : WholePlantState → LeafState leaf
    atmosphereState : WholePlantState → AtmosphereCoupledState atmosphere

    rootToXylemWaterContinuityReference : String
    xylemToLeafWaterContinuityReference : String
    plantWaterStorageReference : String
    transpirationSinkReference : String
    stomatalHydraulicFeedbackReference : String
    photosynthesisWaterStressReference : String
    carbonAssimilationToBiomassReference : String
    nutrientDemandCouplingReference : String
    commonGeometryReference : String
    commonTimeReference : String

open WholePlantHydraulicCarbonWeld public

------------------------------------------------------------------------
-- Conservation and growth coupling.
------------------------------------------------------------------------

record PlantWaterCarbonConservationWeld
    {root : RootSoil.RootSoilIonWaterMechanism}
    {xylem : XylemHydraulicReceipt root}
    {leaf : LeafGasExchangeReceipt}
    {atmosphere : LeafAtmosphereFluidWeld leaf}
    (plant : WholePlantHydraulicCarbonWeld root xylem leaf atmosphere) : Set where
  constructor plantWaterCarbonConservationWeld
  field
    conservation : Conservation.ConservationBundle
    rootUptakeToWaterLedgerReference : String
    transpirationToWaterLedgerReference : String
    storageChangeToWaterLedgerReference : String
    assimilationToCarbonLedgerReference : String
    respirationAndAllocationReference : String
    biomassGrowthReference : String
    nitrogenDemandReference : String
    phosphorusDemandReference : String
    ledgerTimeScaleReference : String

open PlantWaterCarbonConservationWeld public

------------------------------------------------------------------------
-- Stage-7 realization seam.
------------------------------------------------------------------------

record PlantHydraulicCarbonDomainRealization : Set₁ where
  constructor plantHydraulicCarbonDomainRealization
  field
    domainMechanism : Basis.DomainMechanismSocket
    rootSoilMechanism : RootSoil.RootSoilIonWaterMechanism
    xylemHydraulics : XylemHydraulicReceipt rootSoilMechanism
    leafGasExchange : LeafGasExchangeReceipt
    leafAtmosphere : LeafAtmosphereFluidWeld leafGasExchange
    wholePlant :
      WholePlantHydraulicCarbonWeld
        rootSoilMechanism xylemHydraulics leafGasExchange leafAtmosphere
    waterCarbonConservation : PlantWaterCarbonConservationWeld wholePlant

    stateIdentificationReference : String
    controlIdentificationReference : String
    observationIdentificationReference : String
    discrepancyModelReference : String
    experimentDesignReference : String
    identifiabilityReference : String
    heldOutValidationReference : String

open PlantHydraulicCarbonDomainRealization public

tyreeZimmermannDOI : String
tyreeZimmermannDOI = "10.1007/978-3-662-04931-0"

farquharVonCaemmererBerryDOI : String
farquharVonCaemmererBerryDOI = "10.1007/BF00386231"

buckleySackFarquharDOI : String
buckleySackFarquharDOI = "10.1111/pce.12823"

record PlantHydraulicAtmosphereCarbonBoundary : Set where
  constructor plantHydraulicAtmosphereCarbonBoundary
  field
    rootUptakeInstantlyEqualsTranspiration : Bool
    rootUptakeInstantlyEqualsTranspirationIsFalse :
      rootUptakeInstantlyEqualsTranspiration ≡ false

    sameMolarFluxDimensionMeansSameSubstance : Bool
    sameMolarFluxDimensionMeansSameSubstanceIsFalse :
      sameMolarFluxDimensionMeansSameSubstance ≡ false

    c3PhotosynthesisModelIsUniversalPhotosynthesisModel : Bool
    c3PhotosynthesisModelIsUniversalPhotosynthesisModelIsFalse :
      c3PhotosynthesisModelIsUniversalPhotosynthesisModel ≡ false

    optimalWaterEconomyIsUniversalStomatalDynamicLaw : Bool
    optimalWaterEconomyIsUniversalStomatalDynamicLawIsFalse :
      optimalWaterEconomyIsUniversalStomatalDynamicLaw ≡ false

    xylemHydraulicArchitectureAloneDeterminesGrowth : Bool
    xylemHydraulicArchitectureAloneDeterminesGrowthIsFalse :
      xylemHydraulicArchitectureAloneDeterminesGrowth ≡ false

    atmosphereWindReceiptAloneDeterminesLeafGasExchange : Bool
    atmosphereWindReceiptAloneDeterminesLeafGasExchangeIsFalse :
      atmosphereWindReceiptAloneDeterminesLeafGasExchange ≡ false

    wholePlantMechanismNeedsLiteralCommonStateAndConservation : Bool
    wholePlantMechanismNeedsLiteralCommonStateAndConservationIsTrue :
      wholePlantMechanismNeedsLiteralCommonStateAndConservation ≡ true

    stage7ValidationStillRequired : Bool
    stage7ValidationStillRequiredIsTrue :
      stage7ValidationStillRequired ≡ true

canonicalPlantHydraulicAtmosphereCarbonBoundary : PlantHydraulicAtmosphereCarbonBoundary
canonicalPlantHydraulicAtmosphereCarbonBoundary =
  plantHydraulicAtmosphereCarbonBoundary
    false refl
    false refl
    false refl
    false refl
    false refl
    false refl
    true refl
    true refl
