module DASHI.Chemistry.AssayParetoFrontierRefinementExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)

import DASHI.Chemistry.AssayDetectionEnvelopeExact as Assay
import DASHI.Core.ExperimentalCoordinateDesignExact as Design
import DASHI.Core.ProofSearchExperimentalParetoCrossPollinationExact as Cross

------------------------------------------------------------------------
-- CHEMISTRY ASSAY -> RECURSIVE PARETO FRONTIER REFINEMENT
--
-- A coarse analytical report may leave absence/sub-LOD worlds collided.
-- Refinement therefore opens only assay coordinates capable of reducing the
-- current chemical consumer fibre: extraction, matrix, calibration, detector
-- response, or a derived calibrated concentration coordinate.
------------------------------------------------------------------------

data AssayFrontierAxis : Set where
  presenceAxis
  detectionAxis
  quantificationAxis
  extractionAxis
  matrixAxis
  detectorAxis
  calibrationAxis
  : AssayFrontierAxis

axisReference : AssayFrontierAxis → String
axisReference presenceAxis = "chemical presence"
axisReference detectionAxis = "reliable detection"
axisReference quantificationAxis = "reliable quantification"
axisReference extractionAxis = "extraction recovery"
axisReference matrixAxis = "matrix effect"
axisReference detectorAxis = "detector response"
axisReference calibrationAxis = "calibration/derived concentration"

record AssayResidualRefinement : Set where
  constructor assayResidualRefinement
  field
    selectedAxis : AssayFrontierAxis
    assayCoordinate : Assay.AssayCoordinate
    role : Design.CoordinateRole
    residualReference : String
    methodMatrixValidationReference : String
    consumerReference : String

open AssayResidualRefinement public

canonicalCalibrationRefinement : AssayResidualRefinement
canonicalCalibrationRefinement =
  assayResidualRefinement
    calibrationAxis
    Assay.calibratedConcentration
    Design.derivedDiscriminator
    "absence and sub-LOD states remain collided under noReliableSignal"
    "calibration remains analyte x matrix x preparation x instrument relative"
    "chemical presence/detection/quantification consumer"

nonDetectStillCannotCloseAbsence :
  Assay.NonDetectImpliesAbsentPermission → ⊥
nonDetectStillCannotCloseAbsence = Assay.nonDetectCannotAutoPromoteToAbsent

record AssayParetoFrontierBoundary : Set where
  constructor assayParetoFrontierBoundary
  field
    nondetectClosesChemicalAbsence : Bool
    nondetectClosesChemicalAbsenceIsFalse : nondetectClosesChemicalAbsence ≡ false
    assayRefinementMayOpenNuisanceCoordinates : Bool
    assayRefinementMayOpenNuisanceCoordinatesIsTrue : assayRefinementMayOpenNuisanceCoordinates ≡ true
    calibratedDerivedCoordinateIsPhysicalDimension : Bool
    calibratedDerivedCoordinateIsPhysicalDimensionIsFalse : calibratedDerivedCoordinateIsPhysicalDimension ≡ false
    methodMatrixValidationRemainsSeparate : Bool
    methodMatrixValidationRemainsSeparateIsTrue : methodMatrixValidationRemainsSeparate ≡ true

canonicalAssayParetoFrontierBoundary : AssayParetoFrontierBoundary
canonicalAssayParetoFrontierBoundary =
  assayParetoFrontierBoundary false refl true refl false refl true refl

existingExperimentalParetoBoundary : Cross.ProofSearchExperimentalParetoBoundary
existingExperimentalParetoBoundary = Cross.canonicalProofSearchExperimentalParetoBoundary
