module DASHI.Physics.Closure.DrellYanLogLinearShapeLawReceipt where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Agda.Builtin.Unit using (tt)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Core.TypedResidualBasisDecomposition as TRBD
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

data CSSResummationShapeLawStatus : Set where
  cssResummationCandidateNonPromoting :
    CSSResummationShapeLawStatus

  cssResummationShapeLawPromoting :
    CSSResummationShapeLawStatus

record CSSResummationShapeLawReceipt : Setω where
  field
    status :
      CSSResummationShapeLawStatus

    sourceStrictDiagnostic :
      Strict.DrellYanStrictLogLinearSubspaceReceipt

    multiTransitionObstruction :
      DYMultiTransitionObstruction

    artifactPath :
      String

    basisName :
      String

    basisSource :
      String

    protocol :
      String

    transitionPhiStars :
      List String

    transitionScalesFrozenFromSignFlips :
      Bool

    transitionScalesFrozenFromSignFlipsIsTrue :
      transitionScalesFrozenFromSignFlips ≡ true

    residualProjectionBasisConvention :
      String

    residualProjectionChi2PerDof :
      String

    residualProjectionCoverage :
      String

    residualProjectionCondition :
      String

    forwardFitChi2PerDof :
      String

    forwardFitCondition :
      String

    forwardFitOptimizerSuccess :
      Bool

    forwardFitOptimizerSuccessIsTrue :
      forwardFitOptimizerSuccess ≡ true

    gammaSudakovAtNP :
      String

    gammaSudakovAtFO :
      String

    fixedOrderDelta :
      String

    trbdReceipt :
      TRBD.TRBDReceipt String

    structuralDerivationAccepted :
      Bool

    structuralDerivationAcceptedIsFalse :
      structuralDerivationAccepted ≡ false

    strictPassAchieved :
      Bool

    strictPassAchievedIsFalse :
      strictPassAchieved ≡ false

    nonPromoting :
      Bool

    nonPromotingIsTrue :
      nonPromoting ≡ true

    promotingReceiptExists :
      Bool

    promotingReceiptExistsIsFalse :
      promotingReceiptExists ≡ false

    validationCommands :
      List String

    promotionBoundary :
      List String

data ModelGapCandidate : Set where
  wrongPDFSet :
    ModelGapCandidate

  missingElectroweakCorrection :
    ModelGapCandidate

  acceptanceModelGap :
    ModelGapCandidate

  forwardKinematicModelGap :
    ModelGapCandidate

record DYDistributedTheoreticalModelGap : Setω where
  field
    artifactPath :
      String

    protocol :
      String

    branchAssessment :
      String

    totalChi2Direct :
      String

    totalChi2Eigensum :
      String

    modesFor90PctChi2Ranked :
      Nat

    modesFor90PctChi2EigenvalueOrder :
      Nat

    lowRankCovarianceObstruction :
      Bool

    lowRankCovarianceObstructionIsFalse :
      lowRankCovarianceObstruction ≡ false

    largePullBinCount :
      Nat

    discreteFewBinObstruction :
      Bool

    discreteFewBinObstructionIsFalse :
      discreteFewBinObstruction ≡ false

    kinematicScaleFactor :
      String

    kinematicRescaledChi2PerDof :
      String

    kinematicConventionMismatch :
      Bool

    kinematicConventionMismatchIsFalse :
      kinematicConventionMismatch ≡ false

    topPullBins :
      List Nat

    topPullPhiStars :
      List String

    topPullValues :
      List String

    topChi2Eigenmodes :
      List Nat

    modelGapCandidates :
      List ModelGapCandidate

    firstActionableChild :
      String

    firstActionableChildIsAcceptance :
      Bool

    firstActionableChildIsAcceptanceIsTrue :
      firstActionableChildIsAcceptance ≡ true

    physicsCandidatesBlockedUntilAcceptance :
      Bool

    physicsCandidatesBlockedUntilAcceptanceIsTrue :
      physicsCandidatesBlockedUntilAcceptance ≡ true

    promotingReceiptExists :
      Bool

    promotingReceiptExistsIsFalse :
      promotingReceiptExists ≡ false

    gapAssessment :
      List String

record EMSTFullTensorReceipt : Setω where
  field
    reference :
      String

    nStructureFunctionsRequired :
      Nat

    nStructureFunctionsRequiredIsNine :
      nStructureFunctionsRequired ≡ 9

    proxyComponentCount :
      Nat

    proxyComponentCountIsFive :
      proxyComponentCount ≡ 5

    dominantProxyTerm :
      String

    cutsSource :
      String

    leptonicCoefficientMethod :
      String

    chi2LeadPlusA2Proxy :
      String

    chi2FiveComponentProxy :
      String

    fullEMSTSurfaceStatus :
      String

    diagnosticOnly :
      Bool

    diagnosticOnlyIsTrue :
      diagnosticOnly ≡ true

    promotes :
      Bool

    promotesIsFalse :
      promotes ≡ false

    nextIfBlocked :
      String

data AcceptanceMetadataGapStatus : Set where
  acceptanceMetadataGapOpen :
    AcceptanceMetadataGapStatus

record DYAcceptanceMetadataGapReceipt : Setω where
  field
    status :
      AcceptanceMetadataGapStatus

    parentModelGap :
      DYDistributedTheoreticalModelGap

    candidate :
      ModelGapCandidate

    candidateIsAcceptanceModelGap :
      candidate ≡ acceptanceModelGap

    selectionMetadataArtifact :
      String

    datasetLabel :
      String

    ratioTableDoi :
      String

    covarianceTableDoi :
      String

    sqrtSGeV :
      Nat

    atLeastOneJetRequired :
      Bool

    atLeastOneJetRequiredIsTrue :
      atLeastOneJetRequired ≡ true

    acceptanceMetadataStatus :
      String

    comparisonContractStatus :
      String

    missingCriticalFields :
      List String

    missingFieldsCount :
      Nat

    strictLogConflatesAcceptance :
      Bool

    strictLogConflatesAcceptanceIsTrue :
      strictLogConflatesAcceptance ≡ true

    strictLogInterpretation :
      String

    emstReference :
      String

    emstCorrectionStatus :
      String

    emstDerivedScalarKappa :
      String

    emstDerivedScalarChi2PerDof :
      String

    emstDerivedScalarPromotes :
      Bool

    emstDerivedScalarPromotesIsFalse :
      emstDerivedScalarPromotes ≡ false

    emstFullTensorReceipt :
      EMSTFullTensorReceipt

    emstBlockedUntilSelectionMetadataComplete :
      Bool

    emstBlockedUntilSelectionMetadataCompleteIsTrue :
      emstBlockedUntilSelectionMetadataComplete ≡ true

    acceptedByExternalAuthority :
      Bool

    acceptedByExternalAuthorityIsFalse :
      acceptedByExternalAuthority ≡ false

    acceptanceContractComplete :
      Bool

    acceptanceContractCompleteIsFalse :
      acceptanceContractComplete ≡ false

    promotingReceiptExists :
      Bool

    promotingReceiptExistsIsFalse :
      promotingReceiptExists ≡ false

    nextProviderRequest :
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

    cssResummationShapeLawReceipt :
      CSSResummationShapeLawReceipt

    distributedTheoreticalModelGap :
      DYDistributedTheoreticalModelGap

    acceptanceMetadataGapReceipt :
      DYAcceptanceMetadataGapReceipt

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
open CSSResummationShapeLawReceipt public
open DYDistributedTheoreticalModelGap public
open EMSTFullTensorReceipt public
open DYAcceptanceMetadataGapReceipt public
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
        "3135.4985533762156"
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
        ∷ "the point-to-bin-average correction approximation with actual bin widths is blocked at chi2/dof 3135.4985533762156"
        ∷ "log-cubic remains the best compact diagnostic at chi2/dof 18.036622062708705, but no tested basis promotes"
        ∷ []
    }

canonicalCSSResummationTRBDThresholds :
  TRBD.TRBDProtocolThresholds
canonicalCSSResummationTRBDThresholds =
  record
    { coverageThresholdName =
        "diagnostic coverage only"
    ; coverageThreshold =
        "no promotion threshold from coverage alone"
    ; perpendicularThresholdName =
        "strict-log chi2/dof"
    ; perpendicularThreshold =
        "2.0"
    ; thresholdFrozen =
        true
    ; thresholdFrozenIsTrue =
        refl
    }

canonicalCSSResummationTypedBasis :
  TRBD.TypedBasis String
canonicalCSSResummationTypedBasis =
  record
    { basisName =
        "CSS_QCD_resummation_three_component"
    ; basisVectors =
        "log(phiStar * exp(-phiStar^2 / phiStarNP^2))"
        ∷ "log(phiStar * (phiStar / phiStarFO)^(-gammaSudakov(phiStar)))"
        ∷ "log(phiStar^(-deltaFO))"
        ∷ []
    ; basisSource =
        TRBD.causalBasis
    ; notFitted =
        tt
    ; basisSourceDescription =
        "CSS/QCD resummation proxy basis with empirical sign-flip transition scales"
    ; basisPromotionBoundary =
        "the functional form is CSS-motivated, but this artifact is still a diagnostic proxy"
        ∷ "transition scales are frozen from residual sign flips and require an accepted derivation before promotion"
        ∷ "strict-log residual projection remains blocked, so no PromotableTRBDReceipt is inhabited"
        ∷ []
    }

canonicalCSSResummationTRBDReceipt :
  TRBD.TRBDReceipt String
canonicalCSSResummationTRBDReceipt =
  record
    { observed =
        "CMS-SMP-20-003 t43 strict-log data vector"
    ; predicted =
        "sigma_DASHI v4 strict-log prediction vector"
    ; residualConvention =
        "log(prediction) - log(data)"
    ; metricOrCovariance =
        "full propagated strict-log covariance"
    ; basis =
        canonicalCSSResummationTypedBasis
    ; basisCoefficients =
        "-0.05646861716803852"
        ∷ "-0.29104543829985646"
        ∷ "0.1839077444694179"
        ∷ []
    ; rawChi2PerDof =
        "3180.211733150705"
    ; perpendicularChi2PerDof =
        "583.0310302095853"
    ; basisCoverage =
        "0.8472242628449239"
    ; basisCoverageFormula =
        "rho_B = 1 - (perpendicular chi2 / raw chi2)"
    ; coverageHonest =
        refl
    ; thresholds =
        canonicalCSSResummationTRBDThresholds
    ; obstructionStatus =
        TRBD.obstructionTypedPartial "CSS_QCD_resummation_three_component"
    ; projectionArtifact =
        "scripts/data/outputs/dy_slope_decomposition_sigma_dashi_v4_20260515.json"
    ; diagnosticOnly =
        true
    ; promotionBoundary =
        "CSS residual projection is blocked at chi2/dof 583.0310302095853"
        ∷ "CSS positive forward shape fit is blocked at chi2/dof 1577.8709184684762"
        ∷ "the receipt remains non-promoting; no strictPassAchieved proof is supplied"
        ∷ []
    }

canonicalCSSResummationShapeLawReceipt :
  CSSResummationShapeLawReceipt
canonicalCSSResummationShapeLawReceipt =
  record
    { status =
        cssResummationCandidateNonPromoting
    ; sourceStrictDiagnostic =
        Strict.canonicalDrellYanStrictLogLinearSubspaceReceipt
    ; multiTransitionObstruction =
        canonicalDYMultiTransitionObstruction
    ; artifactPath =
        "scripts/data/outputs/dy_slope_decomposition_sigma_dashi_v4_20260515.json"
    ; basisName =
        "CSS_QCD_resummation_three_component"
    ; basisSource =
        "Causal_QCD_CSS_resummation_proxy"
    ; protocol =
        "strict_log_metric"
    ; transitionPhiStars =
        "0.1395"
        ∷ "0.8385"
        ∷ []
    ; transitionScalesFrozenFromSignFlips =
        true
    ; transitionScalesFrozenFromSignFlipsIsTrue =
        refl
    ; residualProjectionBasisConvention =
        "centered and RMS-normalized log component directions"
    ; residualProjectionChi2PerDof =
        "583.0310302095853"
    ; residualProjectionCoverage =
        "0.8472242628449239"
    ; residualProjectionCondition =
        "258.17507686000937"
    ; forwardFitChi2PerDof =
        "1577.8709184684762"
    ; forwardFitCondition =
        "4.1034104834379495"
    ; forwardFitOptimizerSuccess =
        true
    ; forwardFitOptimizerSuccessIsTrue =
        refl
    ; gammaSudakovAtNP =
        "0.09468644955930833"
    ; gammaSudakovAtFO =
        "0.0638246890157665"
    ; fixedOrderDelta =
        "1.0426083906235053"
    ; trbdReceipt =
        canonicalCSSResummationTRBDReceipt
    ; structuralDerivationAccepted =
        false
    ; structuralDerivationAcceptedIsFalse =
        refl
    ; strictPassAchieved =
        false
    ; strictPassAchievedIsFalse =
        refl
    ; nonPromoting =
        true
    ; nonPromotingIsTrue =
        refl
    ; promotingReceiptExists =
        false
    ; promotingReceiptExistsIsFalse =
        refl
    ; validationCommands =
        "python scripts/dy_slope_decomposition.py"
        ∷ "agda -i . -i /usr/share/agda-stdlib DASHI/Physics/Closure/DrellYanLogLinearShapeLawReceipt.agda"
        ∷ []
    ; promotionBoundary =
        "the CSS-derived proxy basis has been tested internally and does not close the strict-log gap"
        ∷ "because both residual projection and positive forward shape fit are blocked, this is not a W3 full-authority input"
        ∷ "remaining branch stays distributed theoretical model gap, with acceptance, EW, PDF, and forward kinematic candidates still live"
        ∷ []
    }

canonicalDYDistributedTheoreticalModelGap :
  DYDistributedTheoreticalModelGap
canonicalDYDistributedTheoreticalModelGap =
  record
    { artifactPath =
        "scripts/data/outputs/dy_slope_decomposition_sigma_dashi_v4_20260515.json"
    ; protocol =
        "strict_log_metric"
    ; branchAssessment =
        "distributed_theoretical_model_gap"
    ; totalChi2Direct =
        "57243.81119671269"
    ; totalChi2Eigensum =
        "57243.81119671269"
    ; modesFor90PctChi2Ranked =
        8
    ; modesFor90PctChi2EigenvalueOrder =
        16
    ; lowRankCovarianceObstruction =
        false
    ; lowRankCovarianceObstructionIsFalse =
        refl
    ; largePullBinCount =
        17
    ; discreteFewBinObstruction =
        false
    ; discreteFewBinObstructionIsFalse =
        refl
    ; kinematicScaleFactor =
        "1.4722228461241493"
    ; kinematicRescaledChi2PerDof =
        "3105.3455095026266"
    ; kinematicConventionMismatch =
        false
    ; kinematicConventionMismatchIsFalse =
        refl
    ; topPullBins =
        0
        ∷ 1
        ∷ 2
        ∷ 3
        ∷ 8
        ∷ []
    ; topPullPhiStars =
        "0.002"
        ∷ "0.006"
        ∷ "0.01"
        ∷ "0.014"
        ∷ "0.0395"
        ∷ []
    ; topPullValues =
        "112.653953"
        ∷ "103.285838"
        ∷ "93.772803"
        ∷ "91.131858"
        ∷ "86.333007"
        ∷ []
    ; topChi2Eigenmodes =
        9
        ∷ 0
        ∷ 15
        ∷ 10
        ∷ 8
        ∷ []
    ; modelGapCandidates =
        wrongPDFSet
        ∷ missingElectroweakCorrection
        ∷ acceptanceModelGap
        ∷ forwardKinematicModelGap
        ∷ []
    ; firstActionableChild =
        "acceptanceModelGap"
    ; firstActionableChildIsAcceptance =
        true
    ; firstActionableChildIsAcceptanceIsTrue =
        refl
    ; physicsCandidatesBlockedUntilAcceptance =
        true
    ; physicsCandidatesBlockedUntilAcceptanceIsTrue =
        refl
    ; promotingReceiptExists =
        false
    ; promotingReceiptExistsIsFalse =
        refl
    ; gapAssessment =
        "covariance chi2 is not low-rank: 8 contribution-ranked eigenmodes are needed for 90 percent of chi2"
        ∷ "the obstruction is not a few-bin artifact: 17 bins have absolute log-space pull above 3"
        ∷ "phiStar rescaling is blocked at chi2/dof 3105.3455095026266 and is only a point-value diagnostic with fixed covariance"
        ∷ "all tested smooth, piecewise, threshold, multiplicative, covariance, discrete-bin, and kinematic-rescaling branches fail"
        ∷ "first actionable child is acceptanceModelGap because strict-log compares a fiducial unfolded table to a predictor without the fiducial acceptance contract"
        ∷ "EW, PDF, and forward kinematic candidates remain live but blocked until the acceptance contract is machine-readable and accepted"
        ∷ []
    }

canonicalEMSTFullTensorReceipt :
  EMSTFullTensorReceipt
canonicalEMSTFullTensorReceipt =
  record
    { reference =
        "arXiv:2006.11382"
    ; nStructureFunctionsRequired =
        9
    ; nStructureFunctionsRequiredIsNine =
        refl
    ; proxyComponentCount =
        5
    ; proxyComponentCountIsFive =
        refl
    ; dominantProxyTerm =
        "A2_like_linear_phiStar"
    ; cutsSource =
        "CMS-SMP-20-003-6b8eb1d"
    ; leptonicCoefficientMethod =
        "deterministic_five_component_angular_proxy"
    ; chi2LeadPlusA2Proxy =
        "4730.167818"
    ; chi2FiveComponentProxy =
        "4162.970858"
    ; fullEMSTSurfaceStatus =
        "missing_nine_component_fiducial_leptonic_coefficients"
    ; diagnosticOnly =
        true
    ; diagnosticOnlyIsTrue =
        refl
    ; promotes =
        false
    ; promotesIsFalse =
        refl
    ; nextIfBlocked =
        "derive the full nine-component EMST fiducial coefficient surface over the exact CMS cuts before EW/PDF lanes are promoted"
    }

canonicalDYAcceptanceMetadataGapReceipt :
  DYAcceptanceMetadataGapReceipt
canonicalDYAcceptanceMetadataGapReceipt =
  record
    { status =
        acceptanceMetadataGapOpen
    ; parentModelGap =
        canonicalDYDistributedTheoreticalModelGap
    ; candidate =
        acceptanceModelGap
    ; candidateIsAcceptanceModelGap =
        refl
    ; selectionMetadataArtifact =
        "scripts/data/outputs/t43_strict_log_sigma_dashi_v4_20260515.json"
    ; datasetLabel =
        "t43_below_Z"
    ; ratioTableDoi =
        "10.17182/hepdata.115656.v1/t43"
    ; covarianceTableDoi =
        "10.17182/hepdata.115656.v1/t44"
    ; sqrtSGeV =
        13000
    ; atLeastOneJetRequired =
        true
    ; atLeastOneJetRequiredIsTrue =
        refl
    ; acceptanceMetadataStatus =
        "fiducial_selection_complete_acceptance_surface_missing"
    ; comparisonContractStatus =
        "non_promoting"
    ; missingCriticalFields =
        "central_acceptance_A"
        ∷ "emst_fiducial_power_correction_surface"
        ∷ []
    ; missingFieldsCount =
        3
    ; strictLogConflatesAcceptance =
        true
    ; strictLogConflatesAcceptanceIsTrue =
        refl
    ; strictLogInterpretation =
        "chi2/dof=3180.211733150705 is informative but not a pure shape-law test until the fiducial acceptance contract is represented"
    ; emstReference =
        "arXiv:2006.11382"
    ; emstCorrectionStatus =
        "blocked_until_central_acceptance_and_fiducial_power_correction_surface_are_machine_readable"
    ; emstDerivedScalarKappa =
        "0.290919"
    ; emstDerivedScalarChi2PerDof =
        "3044.091531"
    ; emstDerivedScalarPromotes =
        false
    ; emstDerivedScalarPromotesIsFalse =
        refl
    ; emstFullTensorReceipt =
        canonicalEMSTFullTensorReceipt
    ; emstBlockedUntilSelectionMetadataComplete =
        true
    ; emstBlockedUntilSelectionMetadataCompleteIsTrue =
        refl
    ; acceptedByExternalAuthority =
        false
    ; acceptedByExternalAuthorityIsFalse =
        refl
    ; acceptanceContractComplete =
        false
    ; acceptanceContractCompleteIsFalse =
        refl
    ; promotingReceiptExists =
        false
    ; promotingReceiptExistsIsFalse =
        refl
    ; nextProviderRequest =
        "CMS-SMP-20-003 t43 fiducial selection metadata is machine-readable: lepton pT/eta, channel triggers, anti-kt R=0.4 jets, jet pT/y, lepton isolation, and channel combination are now sourced from arXiv:2205.04897"
        ∷ "supply or derive the central acceptance surface A(M,phi*) and its provenance"
        ∷ "Pass 20 derived scalar EMST proxy kappa=0.290919 gives chi2/dof=3044.091531 and is non-promoting"
        ∷ "Pass 21 deterministic five-component tensor proxy gives chi2/dof=4162.970858 and is non-promoting"
        ∷ "supply or derive the full nine-component EMST fiducial power-correction surface from the machine-readable CMS cuts; scalar and five-component proxies are insufficient"
        ∷ "only then implement the EMST fiducial power-correction diagnostic as a pre-frozen strict-log prediction correction"
        ∷ "rerun strict-log without posterior retuning before any full W3 authority promotion"
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
    ; cssResummationShapeLawReceipt =
        canonicalCSSResummationShapeLawReceipt
    ; distributedTheoreticalModelGap =
        canonicalDYDistributedTheoreticalModelGap
    ; acceptanceMetadataGapReceipt =
        canonicalDYAcceptanceMetadataGapReceipt
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
        ∷ "stop residual-basis search and resolve the acceptance metadata contract before any further physics correction"
        ∷ []
    }

canonicalDrellYanLogLinearShapeLawReceiptStillOpen :
  shapePassAchieved canonicalDrellYanLogLinearShapeLawReceipt ≡ false
canonicalDrellYanLogLinearShapeLawReceiptStillOpen = refl
