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

data MechanismCandidate : Set where
  resummationTransition :
    String →
    MechanismCandidate

  binIntegrationArtifact :
    Nat →
    MechanismCandidate

  pdfThresholdSlope :
    String →
    MechanismCandidate

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

record DYEndpointThresholdObstruction : Setω where
  field
    artifactPath :
      String

    logCubicChi2PerDof :
      String

    peakBin :
      Nat

    peakPhiStar :
      String

    quadraticCoefficientApproxZero :
      Bool

    quadraticCoefficientApproxZeroIsTrue :
      quadraticCoefficientApproxZero ≡ true

    cubicCoefficientLarge :
      Bool

    cubicCoefficientLargeIsTrue :
      cubicCoefficientLarge ≡ true

    cleanAntisymmetricSignature :
      Bool

    cleanAntisymmetricSignatureIsFalse :
      cleanAntisymmetricSignature ≡ false

    signedWindowBins :
      List Nat

    signedWindowPhiStars :
      List String

    signedWindowResidualSigns :
      List String

    signFlipCount :
      Nat

    signFlipLocations :
      List String

    stepAtPeakChi2PerDof :
      String

    piecewiseLogLinearChi2PerDof :
      String

    stepAtPeakBlocked :
      Bool

    stepAtPeakBlockedIsTrue :
      stepAtPeakBlocked ≡ true

    piecewiseLogLinearBlocked :
      Bool

    piecewiseLogLinearBlockedIsTrue :
      piecewiseLogLinearBlocked ≡ true

    mechanismCandidates :
      List MechanismCandidate

    mechanismAssessment :
      List String

data LobeSign : Set where
  positiveLobe :
    LobeSign

  negativeLobe :
    LobeSign

record DYMultiTransitionObstruction : Setω where
  field
    artifactPath :
      String

    transition1PhiStar :
      String

    transition1Interp :
      String

    transition2PhiStar :
      String

    transition2Interp :
      String

    lobeCount :
      Nat

    lobeStructure :
      List LobeSign

    logCubicChi2PerDof :
      String

    piecewise3RegionChi2PerDof :
      String

    sudakovMatchedChi2PerDof :
      String

    binIntegrationChi2PerDof :
      String

    transitionsAreQCDNatural :
      Bool

    transitionsAreQCDNaturalIsTrue :
      transitionsAreQCDNatural ≡ true

    piecewise3RegionBlocked :
      Bool

    piecewise3RegionBlockedIsTrue :
      piecewise3RegionBlocked ≡ true

    sudakovMatchedBlocked :
      Bool

    sudakovMatchedBlockedIsTrue :
      sudakovMatchedBlocked ≡ true

    binIntegrationBlocked :
      Bool

    binIntegrationBlockedIsTrue :
      binIntegrationBlocked ≡ true

    promotingReceiptExists :
      Bool

    promotingReceiptExistsIsFalse :
      promotingReceiptExists ≡ false

    obstructionAssessment :
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

    endpointThresholdObstruction :
      DYEndpointThresholdObstruction

    multiTransitionObstruction :
      DYMultiTransitionObstruction

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
open DYEndpointThresholdObstruction public
open DYMultiTransitionObstruction public
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

canonicalDYEndpointThresholdObstruction :
  DYEndpointThresholdObstruction
canonicalDYEndpointThresholdObstruction =
  record
    { artifactPath =
        "scripts/data/outputs/dy_slope_decomposition_sigma_dashi_v4_20260515.json"
    ; logCubicChi2PerDof =
        "18.036622062708705"
    ; peakBin =
        17
    ; peakPhiStar =
        "2.215"
    ; quadraticCoefficientApproxZero =
        true
    ; quadraticCoefficientApproxZeroIsTrue =
        refl
    ; cubicCoefficientLarge =
        true
    ; cubicCoefficientLargeIsTrue =
        refl
    ; cleanAntisymmetricSignature =
        false
    ; cleanAntisymmetricSignatureIsFalse =
        refl
    ; signedWindowBins =
        9
        ∷ 10
        ∷ 11
        ∷ 12
        ∷ 13
        ∷ 14
        ∷ 15
        ∷ 16
        ∷ 17
        ∷ []
    ; signedWindowPhiStars =
        "0.051000000000000004"
        ∷ "0.0645"
        ∷ "0.08149999999999999"
        ∷ "0.10250000000000001"
        ∷ "0.1395"
        ∷ "0.21150000000000002"
        ∷ "0.391"
        ∷ "0.8385"
        ∷ "2.215"
        ∷ []
    ; signedWindowResidualSigns =
        "+"
        ∷ "+"
        ∷ "+"
        ∷ "+"
        ∷ "+"
        ∷ "-"
        ∷ "-"
        ∷ "-"
        ∷ "+"
        ∷ []
    ; signFlipCount =
        2
    ; signFlipLocations =
        "0.1395"
        ∷ "0.8385"
        ∷ []
    ; stepAtPeakChi2PerDof =
        "47.561793578554"
    ; piecewiseLogLinearChi2PerDof =
        "47.56179357855403"
    ; stepAtPeakBlocked =
        true
    ; stepAtPeakBlockedIsTrue =
        refl
    ; piecewiseLogLinearBlocked =
        true
    ; piecewiseLogLinearBlockedIsTrue =
        refl
    ; mechanismCandidates =
        resummationTransition "2.215"
        ∷ binIntegrationArtifact 17
        ∷ pdfThresholdSlope "2.215"
        ∷ []
    ; mechanismAssessment =
        "signed residual window is not a clean endpoint antisymmetry: sign flips occur at phiStar 0.1395 and 0.8385"
        ∷ "step-at-peak and piecewise log-linear bases both remain blocked at chi2/dof 47.561793578554"
        ∷ "cubic remains the best tested compact basis but is only partial at chi2/dof 18.036622062708705"
        ∷ "next target is endpoint spike plus midrange sign structure, not a solved threshold law"
        ∷ []
    }

canonicalDYMultiTransitionObstruction :
  DYMultiTransitionObstruction
canonicalDYMultiTransitionObstruction =
  record
    { artifactPath =
        "scripts/data/outputs/dy_slope_decomposition_sigma_dashi_v4_20260515.json"
    ; transition1PhiStar =
        "0.1395"
    ; transition1Interp =
        "non-perturbative to perturbative resummation transition"
    ; transition2PhiStar =
        "0.8385"
    ; transition2Interp =
        "resummation to fixed-order tail transition"
    ; lobeCount =
        3
    ; lobeStructure =
        positiveLobe
        ∷ negativeLobe
        ∷ positiveLobe
        ∷ []
    ; logCubicChi2PerDof =
        "18.036622062708705"
    ; piecewise3RegionChi2PerDof =
        "33.32747844293448"
    ; sudakovMatchedChi2PerDof =
        "2148.233239451757"
    ; binIntegrationChi2PerDof =
        "3117.782816321956"
    ; transitionsAreQCDNatural =
        true
    ; transitionsAreQCDNaturalIsTrue =
        refl
    ; piecewise3RegionBlocked =
        true
    ; piecewise3RegionBlockedIsTrue =
        refl
    ; sudakovMatchedBlocked =
        true
    ; sudakovMatchedBlockedIsTrue =
        refl
    ; binIntegrationBlocked =
        true
    ; binIntegrationBlockedIsTrue =
        refl
    ; promotingReceiptExists =
        false
    ; promotingReceiptExistsIsFalse =
        refl
    ; obstructionAssessment =
        "two sign flips at phiStar 0.1395 and 0.8385 define a three-lobe positive-negative-positive residual after log-linear removal"
        ∷ "the transitions are QCD-natural, but the tested three-region piecewise log-linear basis is blocked at chi2/dof 33.32747844293448"
        ∷ "the tested Sudakov-matched Gaussian/log/power basis is blocked at chi2/dof 2148.233239451757"
        ∷ "the point-to-bin-average correction approximation is blocked at chi2/dof 3117.782816321956"
        ∷ "log-cubic remains the best compact diagnostic at chi2/dof 18.036622062708705, but no tested basis promotes"
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
    ; endpointThresholdObstruction =
        canonicalDYEndpointThresholdObstruction
    ; multiTransitionObstruction =
        canonicalDYMultiTransitionObstruction
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
