module DASHI.Environment.ConstitutiveHydrologyPlantCalibrationExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Environment.LESDomainBasisBidiFrontierExact as Basis
import DASHI.Environment.LESFluidPhysicsCouplingExact as Fluid
import DASHI.Environment.LESPhysicalProcessSourceRegistryExact as Sources
import DASHI.Environment.PlantHydraulicAtmosphereCarbonCouplingExact as Plant
import DASHI.Environment.RootSoilFungalIonWaterPhysiologyExact as RootSoil
import DASHI.Environment.SoilPlantAtmosphereContinuumExact as SPAC
import DASHI.Physics.Units.SI as SI

------------------------------------------------------------------------
-- SOURCE-BOUND CONSTITUTIVE / CALIBRATION LAYER
------------------------------------------------------------------------

richardsSource : Sources.SourceReference
richardsSource = Sources.richards1931

mualemSource : Sources.SourceReference
mualemSource = Sources.mualem1976

vanGenuchtenSource : Sources.SourceReference
vanGenuchtenSource = Sources.vanGenuchten1980

medlynSource : Sources.SourceReference
medlynSource = Sources.medlynEtAl2011

data SoilRetentionModelKind : Set where
  measuredLookup vanGenuchtenRetention applicationSpecificRetention : SoilRetentionModelKind

data SoilConductivityModelKind : Set where
  measuredConductivity mualemConductivity vanGenuchtenMualemConductivity applicationSpecificConductivity : SoilConductivityModelKind

record SoilRetentionConductivityLaw : Set₁ where
  constructor soilRetentionConductivityLaw
  field
    SoilState : Set
    pressureScale conductivityScale storageScale : SI.DecimalScale
    matricPotential : SoilState → SI.Quantity SI.Pressure pressureScale
    volumetricWaterContent : SoilState → SI.Quantity SI.Dimensionless storageScale
    hydraulicConductivity : SoilState → SI.Quantity SI.Velocity conductivityScale
    retentionModel : SoilRetentionModelKind
    conductivityModel : SoilConductivityModelKind
    residualWaterContentReference : String
    saturatedWaterContentReference : String
    saturatedConductivityReference : String
    retentionShapeParameterReference : String
    poreConnectivityParameterReference : String
    fittingDatasetReference : String
    parameterAuthorityReference : String
    independentValidationReference : String
open SoilRetentionConductivityLaw public

record RichardsUnsaturatedFlowReceipt
    (soilLaw : SoilRetentionConductivityLaw) : Set₁ where
  constructor richardsUnsaturatedFlowReceipt
  field
    fluidReduction : Fluid.FluidReductionReceipt
    fluidApplicationIsGroundwater :
      Fluid.application fluidReduction ≡ Fluid.groundwaterOrPorousFlow
    RichardsState : Set
    constitutiveState : RichardsState → SoilState soilLaw
    FluxCarrier StorageChangeCarrier : Set
    darcyFlux : RichardsState → FluxCarrier
    storageChange : RichardsState → StorageChangeCarrier
    richardsResidual : RichardsState → StorageChangeCarrier
    darcyLawReference gravityPotentialReference pressureGradientReference : String
    storageDerivativeReference richardsEquationReference : String
    spatialDiscretisationReference temporalDiscretisationReference : String
    numericalSolverReference massConservationReference : String
    initialBoundaryConditionReference validationReference : String
open RichardsUnsaturatedFlowReceipt public

record SoilHydraulicCalibrationReceipt
    (soilLaw : SoilRetentionConductivityLaw)
    (flow : RichardsUnsaturatedFlowReceipt soilLaw) : Set₁ where
  constructor soilHydraulicCalibrationReceipt
  field
    CalibrationDatum ValidationDatum : Set
    calibrateRetention calibrateConductivity : List CalibrationDatum
    validateRetention validateConductivity validateFlow : List ValidationDatum
    retentionFitCriterionReference conductivityFitCriterionReference : String
    flowFitCriterionReference uncertaintyModelReference : String
    parameterIdentifiabilityReference heldOutSplitReference : String
    acceptedCalibrationReference : String
open SoilHydraulicCalibrationReceipt public

data XylemVulnerabilityModelKind : Set where
  empiricalVulnerabilityCurve segmentedHydraulicNetwork applicationSpecificVulnerability : XylemVulnerabilityModelKind

record XylemConstitutiveCalibration
    {root : RootSoil.RootSoilIonWaterMechanism}
    (xylem : Plant.XylemHydraulicReceipt root) : Set₁ where
  constructor xylemConstitutiveCalibration
  field
    XylemCalibrationState : Set
    xylemState : XylemCalibrationState → Plant.XylemState xylem
    relativeConductanceScale : SI.DecimalScale
    relativeConductance :
      XylemCalibrationState → SI.Quantity SI.Dimensionless relativeConductanceScale
    vulnerabilityModel : XylemVulnerabilityModelKind
    maximumConductanceReference pressureLossReference vulnerabilityCurveReference : String
    capacitanceReference embolismRecoveryOrIrreversibilityReference : String
    temperatureReference calibrationDatasetReference uncertaintyReference : String
    heldOutValidationReference : String
open XylemConstitutiveCalibration public

data StomatalModelKind : Set where
  medlynOptimalEmpirical applicationSpecificStomatalModel : StomatalModelKind

record LeafCarbonWaterCalibration
    (leaf : Plant.LeafGasExchangeReceipt) : Set₁ where
  constructor leafCarbonWaterCalibration
  field
    LeafCalibrationState : Set
    leafState : LeafCalibrationState → Plant.LeafState leaf
    atmosphereState : LeafCalibrationState → Plant.AtmosphereState leaf
    conductanceScale : SI.DecimalScale
    stomatalConductance :
      LeafCalibrationState → SI.Quantity SI.MolarFluxDensity conductanceScale
    co2Scale : SI.DecimalScale
    intercellularCO2Proxy :
      LeafCalibrationState → SI.Quantity SI.Dimensionless co2Scale
    stomatalModel : StomatalModelKind
    medlynG0Reference medlynG1Reference : String
    farquharVcmaxReference farquharJmaxReference respirationReference : String
    temperatureResponseReference vapourPressureDeficitReference lightResponseReference : String
    calibrationDatasetReference uncertaintyReference heldOutValidationReference : String
open LeafCarbonWaterCalibration public

record ConstitutiveSPACMechanism
    (soilLaw : SoilRetentionConductivityLaw)
    (flow : RichardsUnsaturatedFlowReceipt soilLaw)
    (soilCalibration : SoilHydraulicCalibrationReceipt soilLaw flow)
    (soilHydraulics : SPAC.SoilHydraulicBoundaryReceipt)
    (plant : Plant.PlantHydraulicCarbonDomainRealization)
    (spac : SPAC.SoilPlantAtmosphereContinuum soilHydraulics plant)
    (xylemCalibration : XylemConstitutiveCalibration (Plant.xylemHydraulics plant))
    (leafCalibration : LeafCarbonWaterCalibration (Plant.leafGasExchange plant)) : Set₁ where
  constructor constitutiveSPACMechanism
  field
    ConstitutiveState : Set
    soilLawState : ConstitutiveState → SoilState soilLaw
    richardsState : ConstitutiveState → RichardsState flow
    soilHydraulicState : ConstitutiveState → SPAC.SoilHydraulicState soilHydraulics
    spacState : ConstitutiveState → SPAC.SPACState spac
    xylemCalibrationState :
      ConstitutiveState → XylemConstitutiveCalibration.XylemCalibrationState xylemCalibration
    leafCalibrationState :
      ConstitutiveState → LeafCarbonWaterCalibration.LeafCalibrationState leafCalibration
    soilLawToSPACBoundaryReference richardsToSoilBoundaryReference : String
    xylemCalibrationToPlantReference leafCalibrationToPlantReference : String
    rootDemandFeedbackReference atmosphereDemandFeedbackReference : String
    commonGeometryReference commonTimeReference coupledMassBalanceReference : String
    solverAssemblyReference solverVerificationReference : String
open ConstitutiveSPACMechanism public

record ConstitutiveSPACDomainRealization
    (soilLaw : SoilRetentionConductivityLaw)
    (flow : RichardsUnsaturatedFlowReceipt soilLaw)
    (soilCalibration : SoilHydraulicCalibrationReceipt soilLaw flow)
    (soilHydraulics : SPAC.SoilHydraulicBoundaryReceipt)
    (plant : Plant.PlantHydraulicCarbonDomainRealization)
    (spac : SPAC.SoilPlantAtmosphereContinuum soilHydraulics plant)
    (xylemCalibration : XylemConstitutiveCalibration (Plant.xylemHydraulics plant))
    (leafCalibration : LeafCarbonWaterCalibration (Plant.leafGasExchange plant))
    (constitutive : ConstitutiveSPACMechanism soilLaw flow soilCalibration soilHydraulics plant spac xylemCalibration leafCalibration) : Set₁ where
  constructor constitutiveSPACDomainRealization
  field
    domainMechanism : Basis.DomainMechanismSocket
    samePlantDomainMechanism : domainMechanism ≡ Plant.domainMechanism plant
    CalibrationObservation ValidationObservation : Set
    calibrationObservations : List CalibrationObservation
    heldOutObservations : List ValidationObservation
    parameterVectorReference parameterPriorOrBoundsReference : String
    observationOperatorReference discrepancyModelReference calibrationObjectiveReference : String
    identifiabilityReference posteriorOrConfidenceProcedureReference : String
    heldOutValidationReference interventionPredictionReference : String
open ConstitutiveSPACDomainRealization public

record ConstitutiveHydrologyPlantBoundary : Set where
  constructor constitutiveHydrologyPlantBoundary
  field
    richardsEquationAppliesToEveryLESWaterPath : Bool
    richardsEquationAppliesToEveryLESWaterPathIsFalse : richardsEquationAppliesToEveryLESWaterPath ≡ false
    fittedRetentionAutomaticallyValidatesConductivity : Bool
    fittedRetentionAutomaticallyValidatesConductivityIsFalse : fittedRetentionAutomaticallyValidatesConductivity ≡ false
    vanGenuchtenMualemParametersTransferBetweenSoils : Bool
    vanGenuchtenMualemParametersTransferBetweenSoilsIsFalse : vanGenuchtenMualemParametersTransferBetweenSoils ≡ false
    xylemVulnerabilityCalibrationIsUniversalAcrossSpecies : Bool
    xylemVulnerabilityCalibrationIsUniversalAcrossSpeciesIsFalse : xylemVulnerabilityCalibrationIsUniversalAcrossSpecies ≡ false
    medlynParametersAreUniversalAcrossSpeciesAndClimate : Bool
    medlynParametersAreUniversalAcrossSpeciesAndClimateIsFalse : medlynParametersAreUniversalAcrossSpeciesAndClimate ≡ false
    fittedCalibrationIsHeldOutValidation : Bool
    fittedCalibrationIsHeldOutValidationIsFalse : fittedCalibrationIsHeldOutValidation ≡ false
    constitutiveModelNeedsCommonStateAndMassBalance : Bool
    constitutiveModelNeedsCommonStateAndMassBalanceIsTrue : constitutiveModelNeedsCommonStateAndMassBalance ≡ true
    stage7StillNeedsDiscrepancyIdentifiabilityAndHeldOutValidation : Bool
    stage7StillNeedsDiscrepancyIdentifiabilityAndHeldOutValidationIsTrue : stage7StillNeedsDiscrepancyIdentifiabilityAndHeldOutValidation ≡ true

canonicalConstitutiveHydrologyPlantBoundary : ConstitutiveHydrologyPlantBoundary
canonicalConstitutiveHydrologyPlantBoundary =
  constitutiveHydrologyPlantBoundary
    false refl false refl false refl false refl false refl false refl true refl true refl
