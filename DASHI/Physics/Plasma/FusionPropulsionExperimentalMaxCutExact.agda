module DASHI.Physics.Plasma.FusionPropulsionExperimentalMaxCutExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)

import DASHI.Core.ExperimentalCoordinateDesignExact as Design
import DASHI.Physics.Plasma.FusionPropulsionLiteralMaxCutExact as MaxCut
import DASHI.Physics.Materials.FusionPropulsionMaterialSurvivabilityCrossPollinationExact as Materials

------------------------------------------------------------------------
-- LITERAL FRC EXPERIMENTAL COORDINATES
--
-- Natural-number codes are deliberately source-level reported coordinates,
-- not an SI conversion or a claim of exact physical uncertainty.
------------------------------------------------------------------------

record FRCReportedWorld : Set where
  constructor frc-reported-world
  field
    peakDensityCode : Nat
    electronTemperatureCode : Nat
    ionTemperatureCode : Nat
    separatrixRadiusCode : Nat
    reconnectionTimeCode : Nat
    m4AmplitudeCode : Nat

open FRCReportedWorld public

data FRCExperimentalCoordinate : Set where
  peakDensityCoordinate : FRCExperimentalCoordinate
  electronTemperatureCoordinate : FRCExperimentalCoordinate
  ionTemperatureCoordinate : FRCExperimentalCoordinate
  separatrixRadiusCoordinate : FRCExperimentalCoordinate
  reconnectionTimeCoordinate : FRCExperimentalCoordinate
  m4MorphologyCoordinate : FRCExperimentalCoordinate

data FRCExperimentalControl : Set where
  holdReportedWorld : FRCExperimentalControl

data FRCDimension : Set where
  densityDimension : FRCDimension
  energyDimension : FRCDimension
  lengthDimension : FRCDimension
  timeDimension : FRCDimension
  morphologyDimension : FRCDimension

frcRole : FRCExperimentalCoordinate → Design.CoordinateRole
frcRole peakDensityCoordinate = Design.measuredObservable
frcRole electronTemperatureCoordinate = Design.measuredObservable
frcRole ionTemperatureCoordinate = Design.measuredObservable
frcRole separatrixRadiusCoordinate = Design.measuredObservable
frcRole reconnectionTimeCoordinate = Design.measuredObservable
frcRole m4MorphologyCoordinate = Design.derivedDiscriminator

frcDimension : FRCExperimentalCoordinate → FRCDimension
frcDimension peakDensityCoordinate = densityDimension
frcDimension electronTemperatureCoordinate = energyDimension
frcDimension ionTemperatureCoordinate = energyDimension
frcDimension separatrixRadiusCoordinate = lengthDimension
frcDimension reconnectionTimeCoordinate = timeDimension
frcDimension m4MorphologyCoordinate = morphologyDimension

readFRC : FRCExperimentalCoordinate → FRCReportedWorld → Nat
readFRC peakDensityCoordinate = peakDensityCode
readFRC electronTemperatureCoordinate = electronTemperatureCode
readFRC ionTemperatureCoordinate = ionTemperatureCode
readFRC separatrixRadiusCoordinate = separatrixRadiusCode
readFRC reconnectionTimeCoordinate = reconnectionTimeCode
readFRC m4MorphologyCoordinate = m4AmplitudeCode

applyFRCControl : FRCExperimentalControl → FRCReportedWorld → FRCReportedWorld
applyFRCControl holdReportedWorld world = world

frcCoordinateReference : FRCExperimentalCoordinate → String
frcCoordinateReference peakDensityCoordinate =
  "Yingguang-1 peak ion-density comparison"
frcCoordinateReference electronTemperatureCoordinate =
  "Zhu-Wu kinetic electron-temperature prediction"
frcCoordinateReference ionTemperatureCoordinate =
  "Zhu-Wu kinetic ion-temperature prediction"
frcCoordinateReference separatrixRadiusCoordinate =
  "Zhu-Wu kinetic separatrix-radius prediction"
frcCoordinateReference reconnectionTimeCoordinate =
  "whole-device formation-sequence reconnection timing"
frcCoordinateReference m4MorphologyCoordinate =
  "Yingguang-1 camera square-column m=4 morphology"

frcDimensionReference : FRCExperimentalCoordinate → String
frcDimensionReference peakDensityCoordinate = "number density"
frcDimensionReference electronTemperatureCoordinate = "particle energy"
frcDimensionReference ionTemperatureCoordinate = "particle energy"
frcDimensionReference separatrixRadiusCoordinate = "length"
frcDimensionReference reconnectionTimeCoordinate = "time"
frcDimensionReference m4MorphologyCoordinate =
  "dimensionless image-derived Fourier-mode amplitude"

frcCalibrationReference : FRCExperimentalCoordinate → String
frcCalibrationReference peakDensityCoordinate =
  "absolute density diagnostic and uncertainty required"
frcCalibrationReference electronTemperatureCoordinate =
  "electron-temperature diagnostic and uncertainty required"
frcCalibrationReference ionTemperatureCoordinate =
  "ion-temperature diagnostic and uncertainty required"
frcCalibrationReference separatrixRadiusCoordinate =
  "magnetic/image reconstruction and uncertainty required"
frcCalibrationReference reconnectionTimeCoordinate =
  "synchronised circuit/field diagnostic and uncertainty required"
frcCalibrationReference m4MorphologyCoordinate =
  "camera calibration plus declared mode-extraction pipeline required"

frcControlReference : FRCExperimentalControl → String
frcControlReference holdReportedWorld =
  "identity-only reporting control; no physical intervention is claimed"

frcExperimentalDesign :
  Design.ExperimentalCoordinateDesign
    FRCReportedWorld FRCExperimentalControl Nat FRCDimension
frcExperimentalDesign =
  Design.experimentalCoordinateDesign
    FRCExperimentalCoordinate
    frcRole
    frcDimension
    readFRC
    applyFRCControl
    frcCoordinateReference
    frcDimensionReference
    frcCalibrationReference
    frcControlReference

------------------------------------------------------------------------
-- PEAK DENSITY ALONE IS NOT A SUFFICIENT VALIDATION OBSERVER.
------------------------------------------------------------------------

densityOnlyObserver : FRCReportedWorld → Nat
densityOnlyObserver = peakDensityCode

axisymmetricDensityMatch : FRCReportedWorld
axisymmetricDensityMatch = frc-reported-world 22 17 12 1 0 0

observedM4DensityMatch : FRCReportedWorld
observedM4DensityMatch = frc-reported-world 22 17 12 1 0 4

densityObserverCollides :
  densityOnlyObserver axisymmetricDensityMatch ≡
  densityOnlyObserver observedM4DensityMatch
densityObserverCollides = refl

m4SeparatesDensityCollision :
  Design.CoordinateSeparatesCollision frcExperimentalDesign densityOnlyObserver
m4SeparatesDensityCollision =
  Design.coordinateSeparatesCollision
    m4MorphologyCoordinate
    axisymmetricDensityMatch
    observedM4DensityMatch
    refl
    (λ ())

------------------------------------------------------------------------
-- ACQUISITION FRONTIER GENERATED BY THE PHYSICS MAX-CUT.
------------------------------------------------------------------------

data FusionAcquisitionCoordinate : Set where
  shotResolvedDensity : FusionAcquisitionCoordinate
  speciesResolvedTemperature : FusionAcquisitionCoordinate
  separatrixEvolution : FusionAcquisitionCoordinate
  reconnectionTiming : FusionAcquisitionCoordinate
  m4ModeEvolution : FusionAcquisitionCoordinate
  rootPoleDetuning : FusionAcquisitionCoordinate
  energeticRingWidth : FusionAcquisitionCoordinate
  collisionRate : FusionAcquisitionCoordinate
  parallelWaveNumber : FusionAcquisitionCoordinate
  spatialGradientScale : FusionAcquisitionCoordinate
  nonlinearSaturation : FusionAcquisitionCoordinate
  competingDamping : FusionAcquisitionCoordinate
  pb11TargetThickness : FusionAcquisitionCoordinate
  pb11Enrichment : FusionAcquisitionCoordinate
  pb11StoppingPower : FusionAcquisitionCoordinate
  pb11DetectorSolidAngle : FusionAcquisitionCoordinate
  pb11AlphaBranchReconstruction : FusionAcquisitionCoordinate
  nozzleExitDistribution : FusionAcquisitionCoordinate
  coilReactionForce : FusionAcquisitionCoordinate
  measuredThrust : FusionAcquisitionCoordinate

record AcquisitionRequirement : Set where
  constructor acquisition-requirement
  field
    coordinate : FusionAcquisitionCoordinate
    consumer : String
    sameShotOrSameObjectRequired : Bool
    calibrationRequired : Bool
    sourceStatus : MaxCut.EvidenceClass
    acquisitionReference : String

open AcquisitionRequirement public

frcM4Acquisition : AcquisitionRequirement
frcM4Acquisition =
  acquisition-requirement
    m4ModeEvolution
    "simultaneous whole-device FRC formation validation"
    true true
    MaxCut.simulationToExperimentComparison
    "camera morphology must be synchronised to density, temperature, circuit and field traces"

rootPoleDetuningAcquisition : AcquisitionRequirement
rootPoleDetuningAcquisition =
  acquisition-requirement
    rootPoleDetuning
    "robustness region around the exact Qin-Fisch singular limit"
    true true
    MaxCut.analyticOrKineticTheory
    "scan detuning while retaining species-resolved energy-transfer diagnostics"

pb11CrossSectionAcquisition : AcquisitionRequirement
pb11CrossSectionAcquisition =
  acquisition-requirement
    pb11TargetThickness
    "uncertainty-bearing p-B11 reaction-rate posterior"
    true true
    MaxCut.plannedMeasurement
    "RIKEN target development is an acquisition design, not a cross-section result"

thrustAcquisition : AcquisitionRequirement
thrustAcquisition =
  acquisition-requirement
    measuredThrust
    "terminal same-system fusion-propulsion validation"
    true true
    MaxCut.measuredObservation
    "thrust stand, nozzle exit distribution, coil reaction and energy inventory must share shot identity"

------------------------------------------------------------------------
-- MATERIAL-SURVIVABILITY WELDS
--
-- These identify subsystem environments and acquisition consumers only.  They
-- do not transfer oxygen-rich rocket performance or any material lifetime.
------------------------------------------------------------------------

record SameSubsystemMaterialConsumer : Set₁ where
  constructor same-subsystem-material-consumer
  field
    intersection : Materials.FusionPropulsionMaterialIntersection
    expectedEnvironment : Materials.PropulsionMaterialEnvironment
    environmentMatches :
      Materials.environment intersection ≡ expectedEnvironment
    trajectoryOrNozzleSubsystem : String
    LoadHistory Diagnostic : Set
    loadHistory : LoadHistory
    diagnostic : Diagnostic
    sameHardwareReceipt : Set
    survivabilityModelReceipt : Set

open SameSubsystemMaterialConsumer public

record MaterialCrossPollinationBoundary : Set where
  constructor material-cross-pollination-boundary
  field
    environmentIdentityMayGenerateAcquisitionCoordinates : Bool
    environmentIdentityMayGenerateAcquisitionCoordinatesIsTrue :
      environmentIdentityMayGenerateAcquisitionCoordinates ≡ true

    materialIntersectionAloneProvesLifetime : Bool
    materialIntersectionAloneProvesLifetimeIsFalse :
      materialIntersectionAloneProvesLifetime ≡ false

    oxygenRichRocketResultTransfersToFusionNozzle : Bool
    oxygenRichRocketResultTransfersToFusionNozzleIsFalse :
      oxygenRichRocketResultTransfersToFusionNozzle ≡ false

    htsProgrammeIdentityProvesCoilCriticalCurrentUnderShot : Bool
    htsProgrammeIdentityProvesCoilCriticalCurrentUnderShotIsFalse :
      htsProgrammeIdentityProvesCoilCriticalCurrentUnderShot ≡ false

canonicalMaterialCrossPollinationBoundary : MaterialCrossPollinationBoundary
canonicalMaterialCrossPollinationBoundary =
  material-cross-pollination-boundary
    true refl
    false refl
    false refl
    false refl
