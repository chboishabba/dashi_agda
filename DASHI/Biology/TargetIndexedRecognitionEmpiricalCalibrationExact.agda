module DASHI.Biology.TargetIndexedRecognitionEmpiricalCalibrationExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)

import DASHI.Core.AttributedSourceCore as Source
import DASHI.Core.SourceConditionedObservationExact as Observation
import DASHI.Biology.TargetIndexedRecognitionGeometryExact as Geometry
import DASHI.Biology.TargetIndexedRecognitionAdmissibleRegionExact as Region
import DASHI.Biology.IonicMimicrySourceAtlasExact as IonicSources
import DASHI.Biology.KluverLogPolar5HT2ASourceAtlasExact as FiveHT2ASources

------------------------------------------------------------------------
-- EMPIRICAL CALIBRATION SURFACE
--
-- A target-indexed recognition geometry becomes empirical only when every
-- coordinate used by a decision can be bound to:
--
--   target identity
--   pair identity
--   source / artifact
--   assay or structural protocol
--   value / unit / uncertainty semantics
--   coordinate transform
--   threshold / weight calibration.
--
-- Strings below are references, not hidden numerical claims.
------------------------------------------------------------------------

data CalibrationCoordinate : Set where
  chargeCoordinate : CalibrationCoordinate
  sizeShapeCoordinate : CalibrationCoordinate
  donorAcceptorCoordinate : CalibrationCoordinate
  localGeometryCoordinate : CalibrationCoordinate
  coordinationCoordinate : CalibrationCoordinate
  solvationCoordinate : CalibrationCoordinate
  conformationCoordinate : CalibrationCoordinate
  kineticCoordinate : CalibrationCoordinate

data CalibrationEvidenceKind : Set where
  crystallographicGeometry : CalibrationEvidenceKind
  cryoEMGeometry : CalibrationEvidenceKind
  computationalChemistry : CalibrationEvidenceKind
  bindingAssay : CalibrationEvidenceKind
  kineticAssay : CalibrationEvidenceKind
  functionalAssay : CalibrationEvidenceKind
  curatedChemicalIdentity : CalibrationEvidenceKind

record RecognitionCoordinateMeasurement : Set where
  constructor recognitionCoordinateMeasurement
  field
    leftIdentity : String
    rightIdentity : String
    targetIdentity : String
    coordinate : CalibrationCoordinate
    evidenceKind : CalibrationEvidenceKind

    source : Source.AttributedSource
    artifactReference : String
    protocolReference : String
    valueReference : String
    unitReference : String
    uncertaintyReference : String
    coordinateTransformReference : String

    numericValueImported : Bool
    numericValueImportedIsFalse :
      numericValueImported ≡ false

    thresholdCalibrated : Bool
    thresholdCalibratedIsFalse :
      thresholdCalibrated ≡ false

open RecognitionCoordinateMeasurement public

------------------------------------------------------------------------
-- Concrete source-bound qualitative measurements.
------------------------------------------------------------------------

pbCaCoordinationMeasurement : RecognitionCoordinateMeasurement
pbCaCoordinationMeasurement =
  recognitionCoordinateMeasurement
    "Ca2+"
    "Pb2+"
    "protein metal-binding sites"
    coordinationCoordinate
    crystallographicGeometry
    IonicSources.kirbergerYang2008
    "comparative Pb2+/Ca2+ protein-site structural survey"
    "source structural dataset / reported site selection"
    "reported coordination-number / geometry comparison"
    "source-specific coordination convention"
    "source-specific structural uncertainty"
    "future normalized coordination-geometry mismatch adapter"
    false refl
    false refl

pbCaSiteFlexibilityMeasurement : RecognitionCoordinateMeasurement
pbCaSiteFlexibilityMeasurement =
  recognitionCoordinateMeasurement
    "Ca2+"
    "Pb2+"
    "Ca2+-signaling protein site"
    localGeometryCoordinate
    computationalChemistry
    IonicSources.dudevGrauffelLim2018
    "site-class calculations across Ca2+-binding proteins"
    "source computational protocol"
    "rigid/crowded versus flexible/fewer-ligand site behavior"
    "source model coordinate"
    "source model uncertainty / assumptions"
    "future site-flexibility mismatch adapter"
    false refl
    false refl

lsdFiveHT2AConformationMeasurement : RecognitionCoordinateMeasurement
lsdFiveHT2AConformationMeasurement =
  recognitionCoordinateMeasurement
    "serotonin / 5-HT"
    "LSD"
    "human 5-HT2A receptor"
    conformationCoordinate
    cryoEMGeometry
    FiveHT2ASources.gumpperEtAl2025
    "comparative active-state 5-HT2A structural set"
    "source cryo-EM structure-comparison protocol"
    "ligand-dependent receptor-state structural comparison"
    "source structural coordinates"
    "source-reported structural resolution / model uncertainty"
    "future aligned receptor-state displacement / contact mismatch adapter"
    false refl
    false refl

lsdFiveHT2AKineticMeasurement : RecognitionCoordinateMeasurement
lsdFiveHT2AKineticMeasurement =
  recognitionCoordinateMeasurement
    "serotonin / 5-HT"
    "LSD"
    "5-HT2 receptor context"
    kineticCoordinate
    kineticAssay
    FiveHT2ASources.wackerEtAl2017
    "source kinetic observations"
    "source dissociation / signaling assay protocol"
    "slow LSD kinetic coordinate relative to source comparator conditions"
    "source time / rate convention"
    "source-reported uncertainty"
    "future same-target same-protocol kinetic mismatch adapter"
    false refl
    false refl

canonicalRecognitionCoordinateMeasurements :
  List RecognitionCoordinateMeasurement
canonicalRecognitionCoordinateMeasurements =
  pbCaCoordinationMeasurement
  ∷ pbCaSiteFlexibilityMeasurement
  ∷ lsdFiveHT2AConformationMeasurement
  ∷ lsdFiveHT2AKineticMeasurement
  ∷ []

------------------------------------------------------------------------
-- Calibration bundle.
------------------------------------------------------------------------

record RecognitionGeometryEmpiricalCalibration : Set where
  constructor recognitionGeometryEmpiricalCalibration
  field
    geometry : Geometry.TargetRecognitionGeometry
    region : Region.TargetAdmissibleRegion

    measurements : List RecognitionCoordinateMeasurement

    coordinateNormalizationReference : String
    missingCoordinatePolicyReference : String
    thresholdEstimationReference : String
    weightEstimationReference : String
    validationReference : String

    everyWeightedCoordinateHasMeasurement : Bool
    everyWeightedCoordinateHasMeasurementIsFalse :
      everyWeightedCoordinateHasMeasurement ≡ false

    everyHardGateHasMeasurement : Bool
    everyHardGateHasMeasurementIsFalse :
      everyHardGateHasMeasurement ≡ false

    thresholdsEmpiricallyCalibrated : Bool
    thresholdsEmpiricallyCalibratedIsFalse :
      thresholdsEmpiricallyCalibrated ≡ false

    weightsEmpiricallyCalibrated : Bool
    weightsEmpiricallyCalibratedIsFalse :
      weightsEmpiricallyCalibrated ≡ false

    heldOutValidationPassed : Bool
    heldOutValidationPassedIsFalse :
      heldOutValidationPassed ≡ false

open RecognitionGeometryEmpiricalCalibration public

canonicalRecognitionGeometryEmpiricalCalibration :
  RecognitionGeometryEmpiricalCalibration
canonicalRecognitionGeometryEmpiricalCalibration =
  recognitionGeometryEmpiricalCalibration
    Geometry.targetA
    Region.strictCoordinationRegion
    canonicalRecognitionCoordinateMeasurements
    "open: define target-specific normalization after raw coordinate extraction"
    "fail closed: missing required coordinate blocks empirical recognition decision"
    "open: calibrate coordinate tolerances from source-bound train/calibration set"
    "open: fit or declare anisotropic weights before held-out evaluation"
    "open: evaluate target-specific recognition on held-out pairs / structures"
    false refl
    false refl
    false refl
    false refl
    false refl

------------------------------------------------------------------------
-- Source-conditioned-observation firewall reuse.
------------------------------------------------------------------------

sourceObservationBoundary :
  Observation.SourceConditionedObservationBoundary
sourceObservationBoundary =
  Observation.canonicalSourceConditionedObservationBoundary

------------------------------------------------------------------------
-- Promotion conditions.
------------------------------------------------------------------------

record RecognitionCalibrationPromotionGate : Set where
  constructor recognitionCalibrationPromotionGate
  field
    pairAndTargetIdentityFrozen : Bool
    allDecisionCoordinatesMeasured : Bool
    transformFrozenBeforeEvaluation : Bool
    thresholdsFrozenBeforeEvaluation : Bool
    weightsFrozenBeforeEvaluation : Bool
    heldOutPairsPresent : Bool
    heldOutValidationPassed : Bool

open RecognitionCalibrationPromotionGate public

canonicalClosedRecognitionCalibrationGate :
  RecognitionCalibrationPromotionGate
canonicalClosedRecognitionCalibrationGate =
  recognitionCalibrationPromotionGate
    true
    false
    false
    false
    false
    false
    false

data EmpiricalRecognitionGeometryPromoted : Set where

noEmpiricalPromotionFromCurrentCalibration :
  EmpiricalRecognitionGeometryPromoted → ⊥
noEmpiricalPromotionFromCurrentCalibration ()

------------------------------------------------------------------------
-- Boundary.
------------------------------------------------------------------------

record RecognitionCalibrationBoundary : Set where
  constructor recognitionCalibrationBoundary
  field
    sourceGeometryDoesNotAutoDefineMetric : Bool
    sourceGeometryDoesNotAutoDefineMetricIsTrue :
      sourceGeometryDoesNotAutoDefineMetric ≡ true

    qualitativeStructuralDifferenceIsNotNumericDistance : Bool
    qualitativeStructuralDifferenceIsNotNumericDistanceIsTrue :
      qualitativeStructuralDifferenceIsNotNumericDistance ≡ true

    fittedThresholdNeedsHeldOutValidation : Bool
    fittedThresholdNeedsHeldOutValidationIsTrue :
      fittedThresholdNeedsHeldOutValidation ≡ true

    currentGeometryEmpiricallyPromoted : Bool
    currentGeometryEmpiricallyPromotedIsFalse :
      currentGeometryEmpiricallyPromoted ≡ false

open RecognitionCalibrationBoundary public

canonicalRecognitionCalibrationBoundary :
  RecognitionCalibrationBoundary
canonicalRecognitionCalibrationBoundary =
  recognitionCalibrationBoundary
    true refl
    true refl
    true refl
    false refl
