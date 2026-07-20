module DASHI.Empirical.GRQuantumObservableCalibration where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; suc)
open import Agda.Builtin.String using (String)
open import Data.Nat using (_≤_)

------------------------------------------------------------------------
-- Formal observable -> measured quantity discipline.
--
-- This follows the repository's unit-indexed quantity and held-out calibration
-- patterns (`DASHI.Environment.QuantitiesConservation` and
-- `DASHI.Environment.SurrogateCalibration`) without reusing ecology-specific
-- units as physics units.

data PhysicalDimension : Set where
  dimensionless probabilityDimension : PhysicalDimension
  timeDimension lengthDimension massDimension : PhysicalDimension
  energyDimension actionDimension frequencyDimension : PhysicalDimension
  velocityDimension curvatureDimension stressEnergyDimension : PhysicalDimension

data PositiveNat : Set where
  positive : Nat → PositiveNat

positiveValue : PositiveNat → Nat
positiveValue (positive predecessor) = suc predecessor

record PhysicalUnit : Set where
  constructor physical-unit
  field
    name : String
    symbol : String
    dimension : PhysicalDimension
    scaleNumerator : Nat
    scaleDenominator : PositiveNat
    convention : String
    traceabilityReference : String
open PhysicalUnit public

record CalibrationProvenance : Set where
  constructor calibration-provenance
  field
    datasetIdentifier : String
    datasetRevision : String
    instrumentOrSimulation : String
    extractionMethod : String
    analysisVersion : String
    configurationHash : String
    uncertaintyModel : String
    notes : List String
open CalibrationProvenance public

record CalibratedObservable : Set₁ where
  field
    FormalState : Set
    FormalObservable : Set
    Experiment : Set
    MeasuredValue : Set

    extractFormal : FormalState → FormalObservable
    decodePrediction : FormalObservable → MeasuredValue
    readExperiment : Experiment → MeasuredValue

    unit : PhysicalUnit
    provenance : CalibrationProvenance

    calibrationResidual : FormalObservable → Experiment → Nat
    declaredTolerance : Nat
    CalibrationSample : Set
    formalSample : CalibrationSample → FormalObservable
    experimentalSample : CalibrationSample → Experiment
    calibrationWithinTolerance :
      (sample : CalibrationSample) →
      calibrationResidual
        (formalSample sample)
        (experimentalSample sample)
      ≤ declaredTolerance

    normalizationConventionFixed : Set
    normalizationConventionProof : normalizationConventionFixed
    uncertaintyPropagated : Set
    uncertaintyPropagatedProof : uncertaintyPropagated
open CalibratedObservable public

record GRQuantumObservableCalibration : Set₁ where
  field
    properTime : CalibratedObservable
    spatialLength : CalibratedObservable
    energy : CalibratedObservable
    transitionFrequency : CalibratedObservable
    probability : CalibratedObservable
    curvature : CalibratedObservable
    stressEnergy : CalibratedObservable

    commonCoordinateConvention : Set
    commonCoordinateConventionProof : commonCoordinateConvention
    commonSignConvention : Set
    commonSignConventionProof : commonSignConvention
    dimensionalAnalysisClosed : Set
    dimensionalAnalysisClosedProof : dimensionalAnalysisClosed
    calibrationDatasetsIndependentOfFitTargets : Set
    calibrationDatasetsIndependentOfFitTargetsProof :
      calibrationDatasetsIndependentOfFitTargets
open GRQuantumObservableCalibration public

------------------------------------------------------------------------
-- Existing repository reference map.
--
-- These are source pointers, not measurements.  They make the adapters auditable
-- and prevent the new programme from silently replacing existing theorem owners.

record ExistingObservableReferenceMap : Set where
  constructor existing-observable-reference-map
  field
    causalMetricOwner : String
    finiteGeometryOwner : String
    finiteQuantumOwner : String
    einsteinSourceOwner : String
    unitDisciplineOwner : String
    calibrationPatternOwner : String
    finiteDiagnosticOwner : String
open ExistingObservableReferenceMap public

canonicalExistingObservableReferenceMap : ExistingObservableReferenceMap
canonicalExistingObservableReferenceMap =
  existing-observable-reference-map
    "DASHI.Geometry.CausalRelationalMetricSelector"
    "DASHI.Geometry.NonconstantWarpedLorentzianModel"
    "DASHI.Algebra.Quantum.FiniteTreeWeyl"
    "DASHI.Physics.Closure.DiscreteWarpedEinsteinMatterModel"
    "DASHI.Environment.QuantitiesConservation"
    "DASHI.Environment.SurrogateCalibration"
    "DASHI.Unified.GRQuantumFiniteDiagnosticReceipt"

record ObservableCalibrationBoundary : Set where
  constructor observable-calibration-boundary
  field
    typedProgrammeImplemented : Bool
    typedProgrammeImplementedIsTrue : typedProgrammeImplemented ≡ true
    finiteFormalObservablesAvailable : Bool
    finiteFormalObservablesAvailableIsTrue : finiteFormalObservablesAvailable ≡ true
    measuredCalibrationCompleted : Bool
    measuredCalibrationCompletedIsFalse : measuredCalibrationCompleted ≡ false
    physicalUnitsDerivedFromTernaryLabels : Bool
    physicalUnitsDerivedFromTernaryLabelsIsFalse :
      physicalUnitsDerivedFromTernaryLabels ≡ false
open ObservableCalibrationBoundary public

canonicalObservableCalibrationBoundary : ObservableCalibrationBoundary
canonicalObservableCalibrationBoundary =
  observable-calibration-boundary true refl true refl false refl false refl
