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

    chi2PerDofCorrected :
      String

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
        "missing"
    ; slopeDerivation =
        canonicalDASHILogLinearSlopeDerivationRequest
    ; chi2PerDofCorrected =
        "not-yet-computed"
    ; strictPassAchieved =
        false
    ; strictPassAchievedIsFalse =
        refl
    ; shapePassAchieved =
        false
    ; shapePassAchievedIsFalse =
        refl
    ; nextReceiptRequest =
        "replace slopePrediction = missing with a DASHI-derived below-Z log-linear slope"
        ∷ "rerun t43 strict-log diagnostics with the corrected shape law"
        ∷ "only construct a full authority token if strictPassAchieved becomes true"
        ∷ []
    }

canonicalDrellYanLogLinearShapeLawReceiptStillOpen :
  shapePassAchieved canonicalDrellYanLogLinearShapeLawReceipt ≡ false
canonicalDrellYanLogLinearShapeLawReceiptStillOpen = refl
