module DASHI.Environment.ConstitutiveHydrologyPlantCalibrationExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Environment.LESDomainBasisBidiFrontierExact as Basis
import DASHI.Environment.LESFluidPhysicsCouplingExact as Fluid
import DASHI.Environment.LESPhysicalProcessSourceRegistryExact as Sources
import DASHI.Environment.PlantHydraulicAtmosphereCarbonCouplingExact as Plant
import DASHI.Environment.SoilPlantAtmosphereContinuumExact as SPAC
import DASHI.Physics.Units.SI as SI

------------------------------------------------------------------------
-- SOURCE-BOUND CONSTITUTIVE / CALIBRATION LAYER
--
-- Source identities are imported from LESPhysicalProcessSourceRegistryExact.
-- This module consumes those source calibrations and constructs DASHI-specific
-- typed model receipts.  It does not attribute the dependent-state or Stage-7
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
-- conductivity.  The fitting and held-out surfaces stay separately typed.
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
    {root : _}
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
-- molar flux density.  It remains a different physical quantity from CO2 or
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
-- This is the backward-facing socket for Stage-7. Soil hydraulics, xylem and
-- leaf calibration are not merely a list: they must be projections of one
-- state which also projects to the existing SPAC state.
------------------------------------------------------------------------

record ConstitutiveSPACMechanism
    (soilLaw : SoilRetentionConductivityLaw)
    (flow : RichardsUnsaturatedFlowReceipt soilLaw)
    (soilCalibration : SoilHydraulicCalibrationReceipt soilLaw flow)
    (plant : Plant.PlantHydraulicCarbonDomainRealization)
    (spac : SPAC.SoilPlantAtmosphereContinuum
              (SPAC.soilHydraulics
                (record
                  { domainMechanism = Plant.domainMechanism plant
                  ; soilHydraulics = ?
                  })) plant) : Set₁ where
