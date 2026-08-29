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
--
-- Source identities are imported from LESPhysicalProcessSourceRegistryExact.
-- This module consumes those source calibrations and constructs DASHI-specific
-- typed model receipts. It does not attribute the dependent-state or Stage-7
-- architecture to the cited authors.
------------------------------------------------------------------------

richardsSource : Sources.SourceReference
richardsSource = Sources.richards1931

mualemSource : Sources.SourceReference
mualemSource = Sources.mualem1976

vanGenuchtenSource : Sources.SourceReference
vanGenuchtenSource = Sources.vanGenuchten1980

medlynSource : Sources.SourceReference
medlynSource = Sources.medlynEtAl2011

------------------------------------------------------------------------
-- Soil retention / conductivity constitutive surface.
------------------------------------------------------------------------

data SoilRetentionModelKind : Set where
  measuredLookup
  vanGenuchtenRetention
  applicationSpecificRetention
  : SoilRetentionModelKind

data SoilConductivityModelKind : Set where
  measuredConductivity
  mualemConductivity
  vanGenuchtenMualemConductivity
  applicationSpecificConductivity
  : SoilConductivityModelKind

record SoilRetentionConductivityLaw : Set₁ where
  constructor soilRetentionConductivityLaw
  field
    SoilState : Set

    pressureScale : SI.DecimalScale
    conductivityScale : SI.DecimalScale
    storageScale : SI.DecimalScale

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

------------------------------------------------------------------------
-- Richards-style unsaturated flow receipt.
--
-- The equation operator is application-supplied because the repository does
-- not currently have one universal spatial differential-operator carrier. The
-- state variables and constitutive inputs are nevertheless typed and the fluid
-- reduction must be explicitly identified as groundwater/porous flow.
------------------------------------------------------------------------

record RichardsUnsaturatedFlowReceipt
    (soilLaw : SoilRetentionConductivityLaw) : Set₁ where
  constructor richardsUnsaturatedFlowReceipt
  field
    fluidReduction : Fluid.FluidReductionReceipt
    fluidApplicationIsGroundwater :
      Fluid.application fluidReduction ≡ Fluid.groundwaterOrPorousFlow

    RichardsState : Set
    constitutiveState : RichardsState → SoilState soilLaw

    FluxCarrier : Set
    StorageChangeCarrier : Set
    darcyFlux : RichardsState → FluxCarrier
    storageChange : RichardsState → StorageChangeCarrier
    richardsResidual : RichardsState → StorageChangeCarrier

    darcyLawReference : String
    gravityPotentialReference : String
    pressureGradientReference : String
    storageDerivativeReference : String
    richardsEquationReference : String
    spatialDiscretisationReference : String
    temporalDiscretisationReference : String
    numericalSolverReference : String
    massConservationReference : String
    initialBoundaryConditionReference : String
    validationReference : String

open RichardsUnsaturatedFlowReceipt public

------------------------------------------------------------------------
-- Calibration receipt: fitted retention is not automatically validated
-- conductivity. The fitting and held-out surfaces stay separately typed.
------------------------------------------------------------------------

record SoilHydraulicCalibrationReceipt
    (soilLaw : SoilRetentionConductivityLaw)
    (flow : RichardsUnsaturatedFlowReceipt soilLaw) : Set₁ where
  constructor soilHydraulicCalibrationReceipt
  field
    CalibrationDatum : Set
    ValidationDatum : Set

    calibrateRetention : List CalibrationDatum
    calibrateConductivity : List CalibrationDatum
    validateRetention : List ValidationDatum
    validateConductivity : List ValidationDatum
    validateFlow : List ValidationDatum

    retentionFitCriterionReference : String
    conductivityFitCriterionReference : String
    flowFitCriterionReference : String
    uncertaintyModelReference : String
    parameterIdentifiabilityReference : String
    heldOutSplitReference : String
    acceptedCalibrationReference : String

open SoilHydraulicCalibrationReceipt public

------------------------------------------------------------------------
-- Xylem vulnerability / storage calibration.
------------------------------------------------------------------------

data XylemVulnerabilityModelKind : Set where
  empiricalVulnerabilityCurve
  segmentedHydraulicNetwork
  applicationSpecificVulnerability
  : XylemVulnerabilityModelKind

record XylemConstitutiveCalibration
    {root : RootSoil.RootSoilIonWaterMechanism}
    (xylem : Plant.XylemHydraulicReceipt root) : Set₁ where
  constructor xylemConstitutiveCalibration
  field
    CalibrationState : Set
    xylemState : CalibrationState → Plant.XylemState xylem

    relativeConductanceScale : SI.DecimalScale
    relativeConductance :
      CalibrationState → SI.Quantity SI.Dimensionless relativeConductanceScale

    vulnerabilityModel : XylemVulnerabilityModelKind
    maximumConductanceReference : String
    pressureLossReference : String
    vulnerabilityCurveReference : String
    capacitanceReference : String
    embolismRecoveryOrIrreversibilityReference : String
    temperatureReference : String
    calibrationDatasetReference : String
    uncertaintyReference : String
    heldOutValidationReference : String

open XylemConstitutiveCalibration public

------------------------------------------------------------------------
-- Stomatal / photosynthetic calibration.
--
-- Conductance is represented in mol m^-2 s^-1, the same SI dimension as a
-- molar flux density. It remains a different physical quantity from CO2 or
-- water flux and therefore receives a separate named projection.
------------------------------------------------------------------------

data StomatalModelKind : Set where
  medlynOptimalEmpirical
  applicationSpecificStomatalModel
  : StomatalModelKind

record LeafCarbonWaterCalibration
    (leaf : Plant.LeafGasExchangeReceipt) : Set₁ where
  constructor leafCarbonWaterCalibration
  field
    CalibrationState : Set
    leafState : CalibrationState → Plant.LeafState leaf
    atmosphereState : CalibrationState → Plant.AtmosphereState leaf

    conductanceScale : SI.DecimalScale
    stomatalConductance :
      CalibrationState → SI.Quantity SI.MolarFluxDensity conductanceScale

    co2Scale : SI.DecimalScale
    intercellularCO2Proxy :
      CalibrationState → SI.Quantity SI.Dimensionless co2Scale

    stomatalModel : StomatalModelKind
    medlynG0Reference : String
    medlynG1Reference : String
    farquharVcmaxReference : String
    farquharJmaxReference : String
    respirationReference : String
    temperatureResponseReference : String
    vapourPressureDeficitReference : String
    lightResponseReference : String
    calibrationDatasetReference : String
    uncertaintyReference : String
    heldOutValidationReference : String

open LeafCarbonWaterCalibration public

------------------------------------------------------------------------
-- One constitutive SPAC state.
--
-- Soil hydraulics, xylem and leaf calibration are not merely a list: they are
-- required as projections of one state that also projects to the existing SPAC
-- state. This is the reusable producer expected by the Stage-7 consumer.
------------------------------------------------------------------------

record ConstitutiveSPACMechanism
    (soilLaw : SoilRetentionConductivityLaw)
    (flow : RichardsUnsaturatedFlowReceipt soilLaw)
    (soilCalibration : SoilHydraulicCalibrationReceipt soilLaw flow)
    (soilHydraulics : SPAC.SoilHydraulicBoundaryReceipt)
    (plant : Plant.PlantHydraulicCarbonDomainRealization)
    (spac : SPAC.SoilPlantAtmosphereContinuum soilHydraulics plant)
    (xylemCalibration :
      XylemConstitutiveCalibration (Plant.xylemHydraulics plant))
    (leafCalibration :
      LeafCarbonWaterCalibration (Plant.leafGasExchange plant)) : Set₁ where
  constructor constitutiveSPACMechanism
  field
    ConstitutiveState : Set

    soilLawState : ConstitutiveState → SoilState soilLaw
    richardsState : ConstitutiveState → RichardsState flow
    soilHydraulicState : ConstitutiveState → SPAC.SoilHydraulicState soilHydraulics
    spacState : ConstitutiveState → SPAC.SPACState spac
    xylemCalibrationState :
      ConstitutiveState → CalibrationState xylemCalibration
    leafCalibrationState :
      ConstitutiveState → LeafCarbonWaterCalibration.CalibrationState leafCalibration

    soilLawToSPACBoundaryReference : String
    richardsToSoilBoundaryReference : String
    xylemCalibrationToPlantReference : String
    leafCalibrationToPlantReference : String
    rootDemandFeedbackReference : String
    atmosphereDemandFeedbackReference : String
    commonGeometryReference : String
    commonTimeReference : String
    coupledMassBalanceReference : String
    solverAssemblyReference : String
    solverVerificationReference : String

open ConstitutiveSPACMechanism public

------------------------------------------------------------------------
-- Stage-7 / experiment-facing calibration socket.
------------------------------------------------------------------------

record ConstitutiveSPACDomainRealization
    (soilLaw : SoilRetentionConductivityLaw)
    (flow : RichardsUnsaturatedFlowReceipt soilLaw)
    (soilCalibration : SoilHydraulicCalibrationReceipt soilLaw flow)
    (soilHydraulics : SPAC.SoilHydraulicBoundaryReceipt)
    (plant : Plant.PlantHydraulicCarbonDomainRealization)
    (spac : SPAC.SoilPlantAtmosphereContinuum soilHydraulics plant)
    (xylemCalibration :
      XylemConstitutiveCalibration (Plant.xylemHydraulics plant))
    (leafCalibration :
      LeafCarbonWaterCalibration (Plant.leafGasExchange plant))
    (constitutive :
      ConstitutiveSPACMechanism
        soilLaw flow soilCalibration soilHydraulics plant spac
        xylemCalibration leafCalibration) : Set₁ where
  constructor constitutiveSPACDomainRealization
  field
    domainMechanism : Basis.DomainMechanismSocket
    samePlantDomainMechanism : domainMechanism ≡ Plant.domainMechanism plant

    CalibrationObservation : Set
    ValidationObservation : Set
    calibrationObservations : List CalibrationObservation
    heldOutObservations : List ValidationObservation

    parameterVectorReference : String
    parameterPriorOrBoundsReference : String
    observationOperatorReference : String
    discrepancyModelReference : String
    calibrationObjectiveReference : String
    identifiabilityReference : String
    posteriorOrConfidenceProcedureReference : String
    heldOutValidationReference : String
    interventionPredictionReference : String

open ConstitutiveSPACDomainRealization public

record ConstitutiveHydrologyPlantBoundary : Set where
  constructor constitutiveHydrologyPlantBoundary
  field
    richardsEquationAppliesToEveryLESWaterPath : Bool
    richardsEquationAppliesToEveryLESWaterPathIsFalse :
      richardsEquationAppliesToEveryLESWaterPath ≡ false

    fittedRetentionAutomaticallyValidatesConductivity : Bool
    fittedRetentionAutomaticallyValidatesConductivityIsFalse :
      fittedRetentionAutomaticallyValidatesConductivity ≡ false

    vanGenuchtenMualemParametersTransferBetweenSoils : Bool
    vanGenuchtenMualemParametersTransferBetweenSoilsIsFalse :
      vanGenuchtenMualemParametersTransferBetweenSoils ≡ false

    xylemVulnerabilityCalibrationIsUniversalAcrossSpecies : Bool
    xylemVulnerabilityCalibrationIsUniversalAcrossSpeciesIsFalse :
      xylemVulnerabilityCalibrationIsUniversalAcrossSpecies ≡ false

    medlynParametersAreUniversalAcrossSpeciesAndClimate : Bool
    medlynParametersAreUniversalAcrossSpeciesAndClimateIsFalse :
      medlynParametersAreUniversalAcrossSpeciesAndClimate ≡ false

    fittedCalibrationIsHeldOutValidation : Bool
    fittedCalibrationIsHeldOutValidationIsFalse :
      fittedCalibrationIsHeldOutValidation ≡ false

    constitutiveModelNeedsCommonStateAndMassBalance : Bool
    constitutiveModelNeedsCommonStateAndMassBalanceIsTrue :
      constitutiveModelNeedsCommonStateAndMassBalance ≡ true

    stage7StillNeedsDiscrepancyIdentifiabilityAndHeldOutValidation : Bool
    stage7StillNeedsDiscrepancyIdentifiabilityAndHeldOutValidationIsTrue :
      stage7StillNeedsDiscrepancyIdentifiabilityAndHeldOutValidation ≡ true

canonicalConstitutiveHydrologyPlantBoundary : ConstitutiveHydrologyPlantBoundary
canonicalConstitutiveHydrologyPlantBoundary =
  constitutiveHydrologyPlantBoundary
    false refl
    false refl
    false refl
    false refl
    false refl
    false refl
    true refl
    true refl
