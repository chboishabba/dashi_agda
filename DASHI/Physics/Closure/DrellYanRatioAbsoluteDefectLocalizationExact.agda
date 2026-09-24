{-# OPTIONS --safe #-}
module DASHI.Physics.Closure.DrellYanRatioAbsoluteDefectLocalizationExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; []; _∷_)

import DASHI.Physics.Closure.HEPDataW3ComparisonLawReceipt as W3
import DASHI.Physics.Closure.W4CalibrationFailureMechanismExact as W4

------------------------------------------------------------------------
-- CMS DRELL--YAN: RATIO PASS + ABSOLUTE-SHAPE FAILURE
--
-- These are different observables over related source machinery.
-- Therefore the W4 hard negative does NOT logically reject the shared carrier.
-- It localises the next defect search to the extra structure required by the
-- absolute differential projection: normalization, fiducial acceptance,
-- recoil/resummation and tail matching.
--
-- This file deliberately records a diagnostic search preference, not a proof
-- that one named mechanism is the unique cause of the W4 discrepancy.
------------------------------------------------------------------------

data DYObservableProjectionClass : Set where
  adjacentMassWindowRatio : DYObservableProjectionClass
  absoluteZWindowDifferentialShape : DYObservableProjectionClass

data DYDefectLocalizationStatus : Set where
  ratioContactPassAbsoluteProjectionRejected :
    DYDefectLocalizationStatus

record DrellYanRatioAbsoluteDefectLocalization : Set₁ where
  constructor drellYanRatioAbsoluteDefectLocalization
  field
    ratioReceipt : W3.W3ComparisonLawReceipt
    absoluteFailure : W4.W4CalibrationFailureDiagnosis

    ratioProjection : DYObservableProjectionClass
    absoluteProjection : DYObservableProjectionClass

    ratioCriterionSatisfied : Bool
    ratioCriterionSatisfiedIsTrue :
      ratioCriterionSatisfied ≡ true

    absoluteProjectionPromoted : Bool
    absoluteProjectionPromotedIsFalse :
      absoluteProjectionPromoted ≡ false

    ratioChi2PerDofText : String
    absoluteChi2PerDofText : String
    chi2PerDofContrastText : String

    sameUnderlyingCarrierGloballyRejected : Bool
    sameUnderlyingCarrierGloballyRejectedIsFalse :
      sameUnderlyingCarrierGloballyRejected ≡ false

    nextDefectSearchTargetsProjectionSpecificStructure : Bool
    nextDefectSearchTargetsProjectionSpecificStructureIsTrue :
      nextDefectSearchTargetsProjectionSpecificStructure ≡ true

    causalMechanismUniquelyIdentified : Bool
    causalMechanismUniquelyIdentifiedIsFalse :
      causalMechanismUniquelyIdentified ≡ false

    searchTargets : List String
    status : DYDefectLocalizationStatus

open DrellYanRatioAbsoluteDefectLocalization public

canonicalDrellYanRatioAbsoluteDefectLocalization :
  DrellYanRatioAbsoluteDefectLocalization
canonicalDrellYanRatioAbsoluteDefectLocalization =
  drellYanRatioAbsoluteDefectLocalization
    W3.canonicalHEPDataW3ComparisonLawReceipt
    W4.canonicalW4CalibrationFailureDiagnosis
    adjacentMassWindowRatio
    absoluteZWindowDifferentialShape
    (W3.W3ComparisonLawAcceptanceCriterion.criterionSatisfied
      W3.canonicalW3ComparisonLawAcceptanceCriterion)
    refl
    (W4.promotesW4 W4.canonicalW4CalibrationFailureDiagnosis)
    (W4.promotesW4IsFalse W4.canonicalW4CalibrationFailureDiagnosis)
    "2.1565191176275618"
    "298.8462841768543"
    "absolute / ratio chi2-per-dof = 138.57808249139114"
    false refl
    true refl
    false refl
    ( "absolute d-sigma/d-phi-star observable construction"
    ∷ "fiducial leptonic acceptance and observable Jacobian"
    ∷ "low-phi-star recoil / soft-gluon / TMD resummation"
    ∷ "nonperturbative transverse-momentum structure"
    ∷ "fixed-order / matrix-element high-phi-star tail"
    ∷ "physical normalization and unit calibration after shape adequacy"
    ∷ [] )
    ratioContactPassAbsoluteProjectionRejected

w4FailureDoesNotGloballyRejectSharedDYCarrier :
  sameUnderlyingCarrierGloballyRejected
    canonicalDrellYanRatioAbsoluteDefectLocalization
  ≡ false
w4FailureDoesNotGloballyRejectSharedDYCarrier = refl

projectionSpecificSearchIsPreferred :
  nextDefectSearchTargetsProjectionSpecificStructure
    canonicalDrellYanRatioAbsoluteDefectLocalization
  ≡ true
projectionSpecificSearchIsPreferred = refl
