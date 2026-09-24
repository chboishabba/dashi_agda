{-# OPTIONS --safe #-}
module DASHI.Physics.Closure.W4CalibrationFailureMechanismExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; []; _∷_)

data W4CalibrationFailureMechanism : Set where
  globalNormalizationFailure : W4CalibrationFailureMechanism
  binWidthInterpretationFailure : W4CalibrationFailureMechanism
  smoothPhiStarShapeFailure : W4CalibrationFailureMechanism
  missingPhysicalResummationAcceptanceTail : W4CalibrationFailureMechanism

record W4CalibrationFailureDiagnosis : Set where
  constructor w4CalibrationFailureDiagnosis
  field
    currentChi2PerDof : String
    dataEndpointRatio : String
    currentEndpointShapeRatio : String
    widthCorrectedChi2PerDof : String
    massGeneralChi2PerDof : String
    massGeneralBestFitScale : String
    logLinearResidualCoverage : String
    logCubicResidualChi2PerDof : String
    cssProxyResidualChi2PerDof : String
    firstTransitionPhiStar : String
    secondTransitionPhiStar : String
    dominantMechanism : W4CalibrationFailureMechanism
    oneScalarNormalizationIsEnough : Bool
    oneScalarNormalizationIsEnoughIsFalse :
      oneScalarNormalizationIsEnough ≡ false
    nextModelRequirements : List String
    promotesW4 : Bool
    promotesW4IsFalse : promotesW4 ≡ false

open W4CalibrationFailureDiagnosis public

canonicalW4CalibrationFailureDiagnosis : W4CalibrationFailureDiagnosis
canonicalW4CalibrationFailureDiagnosis =
  w4CalibrationFailureDiagnosis
    "298.8462841768543"
    "980.3474210907259"
    "67.15857949369088"
    "297.1653530154906"
    "298.6378875341807"
    "-11.122653052012883"
    "0.9687052128530348"
    "18.036622062708705"
    "583.0310302095853"
    "0.1395"
    "0.8385"
    missingPhysicalResummationAcceptanceTail
    false refl
    ( "preserve the literal differential d-sigma/d-phi-star observable and t22 covariance"
    ∷ "derive rather than posterior-fit the low-phi soft-gluon/TMD resummation and nonperturbative sector"
    ∷ "include the exact CMS fiducial acceptance/leptonic coefficient surface"
    ∷ "match to a controlled fixed-order high-phi tail"
    ∷ "keep physical normalization/unit calibration separate from shape adequacy"
    ∷ "require a held-out or source-derived validation before promotion"
    ∷ [] )
    false refl

currentW4FailureIsNotJustNormalization :
  oneScalarNormalizationIsEnough canonicalW4CalibrationFailureDiagnosis ≡ false
currentW4FailureIsNotJustNormalization = refl
