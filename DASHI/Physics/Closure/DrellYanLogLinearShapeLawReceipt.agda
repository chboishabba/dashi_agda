module DASHI.Physics.Closure.DrellYanLogLinearShapeLawReceipt where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Physics.Closure.DrellYanStrictLogLinearSubspaceReceipt as Strict

------------------------------------------------------------------------
-- Drell-Yan log-linear shape-law target.
--
-- The strict-log diagnostic names span(1, log(phiStar)) as the dominant
-- current obstruction.  This module formalizes the missing slope-law receipt
-- without claiming that the strict chi2/dof <= 2 pass has been achieved.

data LogLinearShapeLawStatus : Set where
  openShapeLawRequest :
    LogLinearShapeLawStatus

  shapeLawStrictPass :
    LogLinearShapeLawStatus

data LogLinearShapeBasisComponent : Set where
  constantOne :
    LogLinearShapeBasisComponent

  logPhiStar :
    LogLinearShapeBasisComponent

data DASHITypedDerivationStatus : Set where
  derivationRequested :
    DASHITypedDerivationStatus

  derivationAccepted :
    DASHITypedDerivationStatus

record DASHITypedDerivation : Setω where
  field
    predictedQuantity :
      String

    derivationStatus :
      DASHITypedDerivationStatus

    sourceLayer :
      String

    accepted :
      Bool

    acceptedIsFalse :
      accepted ≡ false

    openObligations :
      List String

record LogLinearShapeLawReceipt : Setω where
  field
    status :
      LogLinearShapeLawStatus

    diagnosticReceipt :
      Strict.DrellYanStrictLogLinearSubspaceReceipt

    documentedObstruction :
      Strict.ShapeObstructionDocumented

    spanBasis :
      List LogLinearShapeBasisComponent

    spanBasisName :
      String

    slopePrediction :
      String

    slopeDerivation :
      DASHITypedDerivation

    slopeArtifactPath :
      String

    fittedResidualSlopePredMinusData :
      String

    slopeCorrectionNeededForPrediction :
      String

    chi2FractionFromShape :
      String

    chi2PerDofCorrected :
      String

    residualObstructionAfterShapeRemoval :
      Bool

    residualObstructionAfterShapeRemovalIsTrue :
      residualObstructionAfterShapeRemoval ≡ true

    strictPassAchieved :
      Bool

    strictPassAchievedIsFalse :
      strictPassAchieved ≡ false

    shapePassAchieved :
      Bool

    shapePassAchievedIsFalse :
      shapePassAchieved ≡ false

    nextReceiptRequest :
      List String

open DASHITypedDerivation public
open LogLinearShapeLawReceipt public

canonicalDASHILogLinearSlopeDerivationRequest :
  DASHITypedDerivation
canonicalDASHILogLinearSlopeDerivationRequest =
  record
    { predictedQuantity =
        "below-Z phiStar log-linear slope in span(1, log(phiStar))"
    ; derivationStatus =
        derivationRequested
    ; sourceLayer =
        "DASHI typed radiative/depth-averaged correction layer"
    ; accepted =
        false
    ; acceptedIsFalse =
        refl
    ; openObligations =
        "derive the slope from the typed prior stack or radiative correction structure"
        ∷ "freeze the corrected sigma_DASHI predictor before empirical comparison"
        ∷ "recompute the strict-log residual after removing the span(1, log(phiStar)) component"
        ∷ "supply a corrected chi2/dof <= 2 proof before full authority promotion"
        ∷ []
    }

canonicalDrellYanLogLinearShapeLawReceipt :
  LogLinearShapeLawReceipt
canonicalDrellYanLogLinearShapeLawReceipt =
  record
    { status =
        openShapeLawRequest
    ; diagnosticReceipt =
        Strict.canonicalDrellYanStrictLogLinearSubspaceReceipt
    ; documentedObstruction =
        Strict.canonicalSpan1LogPhiStarShapeObstructionDocumented
    ; spanBasis =
        constantOne
        ∷ logPhiStar
        ∷ []
    ; spanBasisName =
        "span(1, log(phiStar))"
    ; slopePrediction =
        "fitted diagnostic only; no DASHI-derived slope prediction accepted"
    ; slopeDerivation =
        canonicalDASHILogLinearSlopeDerivationRequest
    ; slopeArtifactPath =
        "scripts/data/outputs/dy_slope_decomposition_sigma_dashi_v4_20260515.json"
    ; fittedResidualSlopePredMinusData =
        "-0.34242419691254444"
    ; slopeCorrectionNeededForPrediction =
        "0.3424241969125445"
    ; chi2FractionFromShape =
        "0.968705212853035"
    ; chi2PerDofCorrected =
        "111.96455543013676"
    ; residualObstructionAfterShapeRemoval =
        true
    ; residualObstructionAfterShapeRemovalIsTrue =
        refl
    ; strictPassAchieved =
        false
    ; strictPassAchievedIsFalse =
        refl
    ; shapePassAchieved =
        false
    ; shapePassAchievedIsFalse =
        refl
    ; nextReceiptRequest =
        "span(1, log(phiStar)) explains 0.968705212853035 of strict-log chi2 but does not close the receipt"
        ∷ "after fitted shape removal chi2/dof is 111.96455543013676, so a residual obstruction remains"
        ∷ "extend the decomposition beyond the single log-linear slope before any full authority promotion"
        ∷ []
    }

canonicalDrellYanLogLinearShapeLawReceiptStillOpen :
  shapePassAchieved canonicalDrellYanLogLinearShapeLawReceipt ≡ false
canonicalDrellYanLogLinearShapeLawReceiptStillOpen = refl
