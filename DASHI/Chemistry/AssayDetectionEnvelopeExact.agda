module DASHI.Chemistry.AssayDetectionEnvelopeExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Core.ExperimentalCoordinateDesignExact as Design
import DASHI.Core.IntersectionalNonFactorability as NonFactor
import DASHI.Chemistry.RegulatoryAnalyteCoverageBidiExact as Coverage

------------------------------------------------------------------------
-- ANALYTICAL DETECTION ENVELOPE
--
-- Presence, reliable detection and reliable quantification are different
-- coordinates.  A result below a method's validated observation threshold can
-- share the same reportable surface as true absence.  This module deliberately
-- does not assign universal numerical LOD/LOQ values: those belong to an
-- analyte x matrix x preparation x instrument x calibration receipt.
------------------------------------------------------------------------

data TrueAnalyteState : Set where
  trulyAbsent
  presentBelowLOD
  presentBetweenLODAndLOQ
  presentAtOrAboveLOQ
  : TrueAnalyteState

data AssayObservation : Set where
  noReliableSignal
  detectedNotQuantified
  quantifiedSignal
  : AssayObservation

presenceOf : TrueAnalyteState → Coverage.Presence
presenceOf trulyAbsent = Coverage.absent
presenceOf presentBelowLOD = Coverage.present
presenceOf presentBetweenLODAndLOQ = Coverage.present
presenceOf presentAtOrAboveLOQ = Coverage.present

thresholdObservation : TrueAnalyteState → AssayObservation
thresholdObservation trulyAbsent = noReliableSignal
thresholdObservation presentBelowLOD = noReliableSignal
thresholdObservation presentBetweenLODAndLOQ = detectedNotQuantified
thresholdObservation presentAtOrAboveLOQ = quantifiedSignal

absenceAndSubLODShareObservation :
  NonFactor.NonFactorabilityWitness thresholdObservation presenceOf
absenceAndSubLODShareObservation =
  NonFactor.nonFactorabilityWitness
    trulyAbsent
    presentBelowLOD
    refl
    (λ ())

notDetectedCannotRecoverTrueAbsence :
  NonFactor.FactorsThrough thresholdObservation presenceOf → ⊥
notDetectedCannotRecoverTrueAbsence =
  NonFactor.witnessRulesOutEveryFlatFactorisation
    absenceAndSubLODShareObservation

------------------------------------------------------------------------
-- Method-relative thresholds.
------------------------------------------------------------------------

data MethodFamily : Set where
  gasChromatographyMassSpectrometry
  liquidChromatographyMassSpectrometry
  tandemMassSpectrometry
  opticalSpectroscopy
  otherValidatedAnalyticalMethod
  : MethodFamily

data ValidationStatus : Set where
  validatedForDeclaredAnalyteMatrix
  unresolvedForDeclaredAnalyteMatrix
  unsuitableForDeclaredAnalyteMatrix
  : ValidationStatus

record MethodDetectionReceipt : Set where
  constructor methodDetectionReceipt
  field
    analyteReference : String
    matrixReference : String
    extractionReference : String
    cleanupReference : String
    separationReference : String
    signalGenerationReference : String
    detectorReference : String
    calibrationReference : String
    matrixEffectReference : String
    methodFamily : MethodFamily
    validationStatus : ValidationStatus

    -- Integer-scaled carrier chosen by the application.  Unit and scaling are
    -- explicit so a threshold cannot be silently compared across incompatible
    -- concentration languages.
    thresholdUnitReference : String
    lod : Nat
    loq : Nat
    lodAtMostLoq : lod ≤ loq

    decisionRuleReference : String
    provenanceReference : String

open MethodDetectionReceipt public

------------------------------------------------------------------------
-- Analytical mechanism coordinates.
--
-- This cross-pollinates the repository's generic ExperimentalCoordinateDesign:
-- extraction recovery, matrix effects and signal yield are nuisance/systematic
-- coordinates; concentration/detector response are measured coordinates;
-- calibrated concentration is derived.  The same pattern also underlies the
-- atomic/quantum experiment lanes: a physical carrier is observed only through
-- a declared interaction/readout/calibration chain.
------------------------------------------------------------------------

data AssayCoordinate : Set where
  analyteConcentration
  extractionRecovery
  separationResponse
  signalOrIonisationYield
  detectorResponse
  matrixEffect
  calibratedConcentration
  decisionThreshold
  : AssayCoordinate

assayCoordinateRole : AssayCoordinate → Design.CoordinateRole
assayCoordinateRole analyteConcentration = Design.measuredObservable
assayCoordinateRole extractionRecovery = Design.nuisanceCoordinate
assayCoordinateRole separationResponse = Design.nuisanceCoordinate
assayCoordinateRole signalOrIonisationYield = Design.nuisanceCoordinate
assayCoordinateRole detectorResponse = Design.measuredObservable
assayCoordinateRole matrixEffect = Design.nuisanceCoordinate
assayCoordinateRole calibratedConcentration = Design.derivedDiscriminator
assayCoordinateRole decisionThreshold = Design.referenceInvariant

calibratedConcentrationIsDerived :
  assayCoordinateRole calibratedConcentration ≡ Design.derivedDiscriminator
calibratedConcentrationIsDerived = refl

matrixEffectIsNuisanceCoordinate :
  assayCoordinateRole matrixEffect ≡ Design.nuisanceCoordinate
matrixEffectIsNuisanceCoordinate = refl

------------------------------------------------------------------------
-- A molecule can be physically present but observationally inaccessible under
-- a particular method because any stage in the chain is outside its validated
-- envelope.  `InScope` therefore must not be inferred merely from a molecule's
-- existence or a regulatory table entry.
------------------------------------------------------------------------

data MethodCanObserveAnalytePermission : Set where
data NonDetectImpliesAbsentPermission : Set where
data TableLimitDeterminesLODPermission : Set where
data TableLimitDeterminesLOQPermission : Set where

methodScopeCannotBeInferredFromMolecularExistence :
  MethodCanObserveAnalytePermission → ⊥
methodScopeCannotBeInferredFromMolecularExistence ()

nonDetectCannotAutoPromoteToAbsent : NonDetectImpliesAbsentPermission → ⊥
nonDetectCannotAutoPromoteToAbsent ()

tableLimitCannotAutoPromoteToLOD : TableLimitDeterminesLODPermission → ⊥
tableLimitCannotAutoPromoteToLOD ()

tableLimitCannotAutoPromoteToLOQ : TableLimitDeterminesLOQPermission → ⊥
tableLimitCannotAutoPromoteToLOQ ()

record AssayDetectionBoundary : Set where
  constructor assayDetectionBoundary
  field
    chemicalPresenceEqualsDetection : Bool
    chemicalDetectionEqualsQuantification : Bool
    nonDetectMeansChemicalAbsence : Bool
    lodAndLoqAreMethodMatrixRelative : Bool
    extractionAndMatrixEffectsAreObservationCoordinates : Bool
    quantumAtomicReadoutStructureImpliesSameInstrumentMechanism : Bool

canonicalAssayDetectionBoundary : AssayDetectionBoundary
canonicalAssayDetectionBoundary =
  assayDetectionBoundary false false false true true false
