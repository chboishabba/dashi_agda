module DASHI.Environment.FiniteSPACCalibrationExperimentExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Environment.LESPhysicalProcessSourceRegistryExact as Sources
import DASHI.Environment.ConstitutiveHydrologyPlantCalibrationExact as Constitutive

------------------------------------------------------------------------
-- FINITE CALIBRATION / EXPERIMENT CARRIER
--
-- Repository-native experiment architecture built on the already source-bound
-- Richards / Mualem / van Genuchten / xylem / Farquhar / Medlyn owners.
-- Scientific formulas and model provenance remain with those owners and the
-- typed source registry.  This module only fixes the finite experimental roles
-- needed to instantiate one system without confusing fit and validation data.
------------------------------------------------------------------------

data SoilParameter : Set where
  thetaResidual thetaSaturated alphaVG nVG saturatedConductivity poreConnectivity
  : SoilParameter

data XylemParameter : Set where
  maximumConductance vulnerabilityMidpoint vulnerabilitySlope capacitance
  : XylemParameter

data LeafParameter : Set where
  medlynG0 medlynG1 farquharVcmax farquharJmax leafRespiration
  : LeafParameter

data ParameterKind : Set where
  soilParameter : SoilParameter → ParameterKind
  xylemParameter : XylemParameter → ParameterKind
  leafParameter : LeafParameter → ParameterKind

data MeasurementKind : Set where
  soilWaterContent
  soilMatricPotential
  soilHydraulicConductivity
  soilFlux
  xylemWaterPotential
  sapFlow
  relativeXylemConductance
  leafTranspiration
  leafAssimilation
  stomatalConductance
  vapourPressureDeficit
  leafTemperature
  light
  atmosphericCO2
  precipitation
  wind
  : MeasurementKind

data ExperimentRole : Set where
  calibration heldOutValidation interventionTest : ExperimentRole

data Compartment : Set where
  soil root xylem leaf atmosphere : Compartment

record ParameterSlot : Set where
  constructor parameterSlot
  field
    kind : ParameterKind
    valueReference : String
    unitOrDimensionReference : String
    priorOrBoundReference : String
    authorityReference : String

open ParameterSlot public

record ObservationSlot : Set where
  constructor observationSlot
  field
    kind : MeasurementKind
    compartment : Compartment
    role : ExperimentRole
    timeReference : String
    spatialReference : String
    valueReference : String
    uncertaintyReference : String
    instrumentOrDatasetReference : String

open ObservationSlot public

record ForcingSlot : Set where
  constructor forcingSlot
  field
    kind : MeasurementKind
    timeReference : String
    valueReference : String
    uncertaintyReference : String
    sourceReference : String

open ForcingSlot public

record FiniteSPACCalibrationExperiment : Set where
  constructor finiteSPACCalibrationExperiment
  field
    siteReference : String
    speciesReference : String
    seasonReference : String
    soilProfileReference : String

    parameters : List ParameterSlot
    observations : List ObservationSlot
    forcings : List ForcingSlot

    calibrationWindowReference : String
    heldOutWindowReference : String
    interventionWindowReference : String
    observationOperatorReference : String
    discrepancyModelReference : String
    parameterIdentifiabilityReference : String
    posteriorOrConfidenceReference : String
    coupledSolverReference : String
    massBalanceReference : String
    independentValidationReference : String

open FiniteSPACCalibrationExperiment public

------------------------------------------------------------------------
-- The source-bounded model families consumed by the design.
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
-- Fit and validation are explicit labels, so a datum cannot silently become
-- both by virtue of belonging to the same list or time series.
------------------------------------------------------------------------

record FitValidationSeparationWitness
    (fit validation : ObservationSlot) : Set where
  constructor fitValidationSeparationWitness
  field
    fitIsCalibration : role fit ≡ calibration
    validationIsHeldOut : role validation ≡ heldOutValidation

open FitValidationSeparationWitness public

record FiniteSPACExperimentBoundary : Set where
  constructor finiteSPACExperimentBoundary
  field
    parameterNameIsCalibratedValue : Bool
    parameterNameIsCalibratedValueIsFalse : parameterNameIsCalibratedValue ≡ false

    oneDatasetMaySilentlyServeFitAndHeldOutValidation : Bool
    oneDatasetMaySilentlyServeFitAndHeldOutValidationIsFalse :
      oneDatasetMaySilentlyServeFitAndHeldOutValidation ≡ false

    sameModelFamilyMeansSameParameterValuesAcrossSites : Bool
    sameModelFamilyMeansSameParameterValuesAcrossSitesIsFalse :
      sameModelFamilyMeansSameParameterValuesAcrossSites ≡ false

    finiteExperimentCanInstantiateConstitutiveSPACArchitecture : Bool
    finiteExperimentCanInstantiateConstitutiveSPACArchitectureIsTrue :
      finiteExperimentCanInstantiateConstitutiveSPACArchitecture ≡ true

    experimentDesignAloneProvesStage7Validation : Bool
    experimentDesignAloneProvesStage7ValidationIsFalse :
      experimentDesignAloneProvesStage7Validation ≡ false

open FiniteSPACExperimentBoundary public

canonicalFiniteSPACExperimentBoundary : FiniteSPACExperimentBoundary
canonicalFiniteSPACExperimentBoundary =
  finiteSPACExperimentBoundary false refl false refl false refl true refl false refl

-- Keep the constitutive owner imported as the target architecture.  This value
-- is intentionally only a repository identifier; actual instantiation remains
-- application-specific and must supply all dependent receipts.
constitutiveSPACOwnerReference : String
constitutiveSPACOwnerReference =
  "DASHI.Environment.ConstitutiveHydrologyPlantCalibrationExact"
