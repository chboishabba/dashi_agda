{-# OPTIONS --safe #-}
module DASHI.Physics.Closure.W4CalibrationBidiAttemptExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)

import DASHI.Physics.Closure.W4ZAdequacyReceipt as Adequacy
import DASHI.Physics.Closure.W4ZPeakCalibrationAnchorReceipt as Anchor

data W4CalibrationAttemptOutcome : Set where
  currentCandidateRejectedByResidual :
    W4CalibrationAttemptOutcome
  candidatePassesLocalResidual :
    W4CalibrationAttemptOutcome

canonicalDirtyCandidateOutcome : W4CalibrationAttemptOutcome
canonicalDirtyCandidateOutcome =
  currentCandidateRejectedByResidual

dirtyAdequacyResult :
  Adequacy.W4ZAdequacyResult
dirtyAdequacyResult =
  Adequacy.canonicalDirtyZPeakObstructedResult

dirtyAdequacyIsFalse :
  Adequacy.W4ZAdequacyResult.adequate dirtyAdequacyResult ≡ false
dirtyAdequacyIsFalse =
  refl

dirtyAdequacyStatusIsObstructed :
  Adequacy.W4ZAdequacyResult.status dirtyAdequacyResult
  ≡ Adequacy.obstructedUnderTypedThreshold
dirtyAdequacyStatusIsObstructed =
  refl

dirtyAnchorDiagnostic :
  Anchor.W4ZPeakCalibrationAnchorMissingArtifactDiagnostic
dirtyAnchorDiagnostic =
  Anchor.canonicalW4ZPeakCalibrationAnchorMissingArtifactDiagnostic

dirtyAnchorStatusIsInadequate :
  Anchor.W4ZPeakCalibrationAnchorMissingArtifactDiagnostic.status
    dirtyAnchorDiagnostic
  ≡ Anchor.preparedWithT21T22ArtifactsAndInadequateShapeFit
dirtyAnchorStatusIsInadequate =
  refl

record W4CalibrationBidiReceipt : Set where
  constructor w4CalibrationBidiReceipt
  field
    attemptRan : Bool
    attemptRanIsTrue : attemptRan ≡ true
    outcome : W4CalibrationAttemptOutcome
    outcomeIsRejected :
      outcome ≡ currentCandidateRejectedByResidual
    fittedScale : String
    chi2PerDof : String
    firstBinPull : String
    lastBinPull : String
    adequacyDecision : Bool
    adequacyDecisionIsFalse : adequacyDecision ≡ false
    externalDYAuthorityPresent : Bool
    externalDYAuthorityPresentIsFalse :
      externalDYAuthorityPresent ≡ false
    candidate256PhysicalCalibrationPromoted : Bool
    candidate256PhysicalCalibrationPromotedIsFalse :
      candidate256PhysicalCalibrationPromoted ≡ false
    replacementRequired : Bool
    replacementRequiredIsTrue :
      replacementRequired ≡ true

open W4CalibrationBidiReceipt public

canonicalW4CalibrationBidiReceipt :
  W4CalibrationBidiReceipt
canonicalW4CalibrationBidiReceipt =
  w4CalibrationBidiReceipt
    true refl
    canonicalDirtyCandidateOutcome refl
    "230534508.31238452"
    "298.8462841768543"
    "-67.35457265472463"
    "-51.62836040061707"
    (Adequacy.W4ZAdequacyResult.adequate dirtyAdequacyResult)
    dirtyAdequacyIsFalse
    false refl
    false refl
    true refl

currentW4CandidateIsNotAnOpenUnknown :
  W4CalibrationBidiReceipt.outcome canonicalW4CalibrationBidiReceipt
  ≡ currentCandidateRejectedByResidual
currentW4CandidateIsNotAnOpenUnknown =
  refl
