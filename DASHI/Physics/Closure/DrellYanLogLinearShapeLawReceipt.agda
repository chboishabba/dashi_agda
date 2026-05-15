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

  logPhiStarSquared :
    LogLinearShapeBasisComponent

  logPhiStarCubed :
    LogLinearShapeBasisComponent

data ExtendedLogPolynomialStatus : Set where
  logQuadraticBlocked :
    ExtendedLogPolynomialStatus

  logCubicPartial :
    ExtendedLogPolynomialStatus

  localizedResidualTargetOpen :
    ExtendedLogPolynomialStatus

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

record LogPolynomialDecompositionReceipt : Setω where
  field
    status :
      ExtendedLogPolynomialStatus

    artifactPath :
      String

    basisSource :
      String

    logLinearBasis :
      List LogLinearShapeBasisComponent

    logLinearPerpChi2PerDof :
      String

    logLinearCoverage :
      String

    logQuadraticBasis :
      List LogLinearShapeBasisComponent

    logQuadraticPerpChi2PerDof :
      String

    logQuadraticCoverage :
      String

    logQuadraticCoefficients :
      List String

    logQuadraticBlockedFlag :
      Bool

    logQuadraticBlockedFlagIsTrue :
      logQuadraticBlockedFlag ≡ true

    logCubicBasis :
      List LogLinearShapeBasisComponent

    logCubicPerpChi2PerDof :
      String

    logCubicCoverage :
      String

    logCubicCoefficients :
      List String

    logCubicPartialFlag :
      Bool

    logCubicPartialFlagIsTrue :
      logCubicPartialFlag ≡ true

    peakResidualBinAfterLinear :
      Nat

    peakResidualPhiStarAfterLinear :
      String

    peakResidualPerBinChi2DiagApprox :
      String

    topResidualPhiStarsAfterLinear :
      List String

    promotability :
      Bool

    promotabilityIsFalse :
      promotability ≡ false

    nextBasisRequest :
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

    extendedLogPolynomialReceipt :
      LogPolynomialDecompositionReceipt

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
open LogPolynomialDecompositionReceipt public
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

canonicalDrellYanLogPolynomialDecompositionReceipt :
  LogPolynomialDecompositionReceipt
canonicalDrellYanLogPolynomialDecompositionReceipt =
  record
    { status =
        logCubicPartial
    ; artifactPath =
        "scripts/data/outputs/dy_slope_decomposition_sigma_dashi_v4_20260515.json"
    ; basisSource =
        "Structural_QCD_log_series"
    ; logLinearBasis =
        constantOne
        ∷ logPhiStar
        ∷ []
    ; logLinearPerpChi2PerDof =
        "111.96455543013676"
    ; logLinearCoverage =
        "0.9687052128530348"
    ; logQuadraticBasis =
        constantOne
        ∷ logPhiStar
        ∷ logPhiStarSquared
        ∷ []
    ; logQuadraticPerpChi2PerDof =
        "116.35250713772491"
    ; logQuadraticCoverage =
        "0.9695113310840124"
    ; logQuadraticCoefficients =
        "-0.3456040018237741"
        ∷ "-0.37520820716245223"
        ∷ "-0.005629554053299893"
        ∷ []
    ; logQuadraticBlockedFlag =
        true
    ; logQuadraticBlockedFlagIsTrue =
        refl
    ; logCubicBasis =
        constantOne
        ∷ logPhiStar
        ∷ logPhiStarSquared
        ∷ logPhiStarCubed
        ∷ []
    ; logCubicPerpChi2PerDof =
        "18.036622062708705"
    ; logCubicCoverage =
        "0.9955888208070182"
    ; logCubicCoefficients =
        "-0.261608474568653"
        ∷ "-0.19810845664320986"
        ∷ "0.08021870293046186"
        ∷ "0.010077661408074227"
        ∷ []
    ; logCubicPartialFlag =
        true
    ; logCubicPartialFlagIsTrue =
        refl
    ; peakResidualBinAfterLinear =
        17
    ; peakResidualPhiStarAfterLinear =
        "2.215"
    ; peakResidualPerBinChi2DiagApprox =
        "643.3263320985052"
    ; topResidualPhiStarsAfterLinear =
        "2.215"
        ∷ "0.0395"
        ∷ "0.0315"
        ∷ "0.051000000000000004"
        ∷ "0.026500000000000003"
        ∷ []
    ; promotability =
        false
    ; promotabilityIsFalse =
        refl
    ; nextBasisRequest =
        "quadratic log basis is blocked: chi2/dof increases to 116.35250713772491"
        ∷ "cubic log basis is partial: chi2/dof drops to 18.036622062708705 but remains above 2"
        ∷ "largest post-linear localized residual is bin 17 at phiStar 2.215"
        ∷ "next typed target should test endpoint threshold or bin-integration structure before promotion"
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
    ; extendedLogPolynomialReceipt =
        canonicalDrellYanLogPolynomialDecompositionReceipt
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
