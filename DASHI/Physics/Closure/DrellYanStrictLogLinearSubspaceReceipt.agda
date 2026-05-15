module DASHI.Physics.Closure.DrellYanStrictLogLinearSubspaceReceipt where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Agda.Builtin.Unit using (tt)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Core.TypedResidualBasisDecomposition as TRBD

------------------------------------------------------------------------
-- Corrected strict Drell-Yan log-covariance diagnosis.
--
-- This module records the result of the t43 strict-log diagnostics after
-- adding diagonal/full covariance and log-linear subspace decomposition.
-- It is a receipt for a negative strict-pass result and a positive diagnosis
-- of the failure mode, not a strict Drell-Yan promotion.

data StrictLogDiagnosticPredictor : Set where
  phiStarRatioPredictor :
    StrictLogDiagnosticPredictor

  sigmaDashiV4Predictor :
    StrictLogDiagnosticPredictor

data StrictLogConjectureStatus : Set where
  empiricallyRefuted :
    StrictLogConjectureStatus

  empiricallySupported :
    StrictLogConjectureStatus

data StrictLogFirstMissing : Set where
  missingDepthAveragedKernelImplementation :
    StrictLogFirstMissing

  missingSpan1LogPhiStarShapeLaw :
    StrictLogFirstMissing

  missingLogLinearOrthogonalityProof :
    StrictLogFirstMissing

  missingInterceptMatchProof :
    StrictLogFirstMissing

  missingResidualComplementBound :
    StrictLogFirstMissing

  missingStrictPassReceipt :
    StrictLogFirstMissing

data StrictLogShapeObstruction : Set where
  span1LogPhiStar :
    StrictLogShapeObstruction

record ShapeObstructionDocumented : Set where
  field
    shapeObstruction :
      StrictLogShapeObstruction

    obstructionDocumented :
      Bool

    obstructionDocumentedIsTrue :
      obstructionDocumented ≡ true

    obstructionSummary :
      String

    nextOpenRequest :
      String

open ShapeObstructionDocumented public

record StrictLogDiagnosticNumbers : Set where
  field
    predictor :
      StrictLogDiagnosticPredictor

    artifactPath :
      String

    projectionDigest :
      String

    strictChi2PerDof :
      String

    diagonalOnlyChi2PerDof :
      String

    fullOverDiagonalChi2 :
      String

    offDiagonalContributionFraction :
      String

    leadingInverseCovarianceModeFraction :
      String

    logLinearSubspaceChi2Fraction :
      String

    orthogonalComplementChi2Fraction :
      String

    strictProtocolPass :
      Bool

    strictProtocolPassIsFalse :
      strictProtocolPass ≡ false

open StrictLogDiagnosticNumbers public

phiStarRatioStrictLogDiagnosticNumbers :
  StrictLogDiagnosticNumbers
phiStarRatioStrictLogDiagnosticNumbers =
  record
    { predictor =
        phiStarRatioPredictor
    ; artifactPath =
        "scripts/data/outputs/t43_strict_log_phi_star_ratio_20260515.json"
    ; projectionDigest =
        "11fd7665435b9d540288def8702f587897bd4412a5f4c10ab500c06d14258317"
    ; strictChi2PerDof =
        "283.45739523864586"
    ; diagonalOnlyChi2PerDof =
        "326.09046767953845"
    ; fullOverDiagonalChi2 =
        "0.8692599855976478"
    ; offDiagonalContributionFraction =
        "-0.15040381079138665"
    ; leadingInverseCovarianceModeFraction =
        "0.006612430351796318"
    ; logLinearSubspaceChi2Fraction =
        "0.890463699129403"
    ; orthogonalComplementChi2Fraction =
        "0.10953630087059682"
    ; strictProtocolPass =
        false
    ; strictProtocolPassIsFalse =
        refl
    }

sigmaDashiV4StrictLogDiagnosticNumbers :
  StrictLogDiagnosticNumbers
sigmaDashiV4StrictLogDiagnosticNumbers =
  record
    { predictor =
        sigmaDashiV4Predictor
    ; artifactPath =
        "scripts/data/outputs/t43_strict_log_sigma_dashi_v4_20260515.json"
    ; projectionDigest =
        "5add6664851b44fc8c46307024ea73cc12c18dcaf76d342c061b870adf64c554"
    ; strictChi2PerDof =
        "3180.211733150705"
    ; diagonalOnlyChi2PerDof =
        "5219.418540183218"
    ; fullOverDiagonalChi2 =
        "0.6093038350281581"
    ; offDiagonalContributionFraction =
        "-0.6412173081986042"
    ; leadingInverseCovarianceModeFraction =
        "0.012596343284573172"
    ; logLinearSubspaceChi2Fraction =
        "0.9687052128530349"
    ; orthogonalComplementChi2Fraction =
        "0.031294787146965215"
    ; strictProtocolPass =
        false
    ; strictProtocolPassIsFalse =
        refl
    }

record LogLinearSubspaceTheoremSurface : Setω where
  field
    LogResidualVector :
      Set

    LogCovarianceInverse :
      Set

    LogLinearSubspace :
      Set

    projectionOntoLogLinearSubspace :
      LogResidualVector →
      LogLinearSubspace

    chi2Norm :
      LogResidualVector →
      Set

    logLinearDominanceLaw :
      LogResidualVector →
      Set

record StrictPassOrthogonalityObligation : Setω where
  field
    Depth :
      Set

    Kernel :
      Set

    LogResidualVector :
      Set

    LogLinearSubspace :
      Set

    alphaSlope :
      Depth →
      Depth →
      Set

    interceptMatch :
      Kernel →
      Kernel →
      Set

    depthMeanEq :
      Depth →
      Depth →
      Set

    orthogonalToLogLinearSubspace :
      LogResidualVector →
      LogLinearSubspace →
      Set

    residualComplementBound :
      LogResidualVector →
      Nat →
      Set

record DepthAveragedCurvatureCandidate : Setω where
  field
    Depth :
      Set

    PhiStar :
      Set

    DepthMeasure :
      Set

    depthAveragedKernel :
      PhiStar →
      Depth →
      Depth →
      DepthMeasure →
      Set

    analyticUniformDepthKernel :
      String

    createsLogPhiCurvature :
      Bool

    createsLogPhiCurvatureIsTrue :
      createsLogPhiCurvature ≡ true

    promotionBoundary :
      List String

open DepthAveragedCurvatureCandidate public

record StrictLogObstructionWitness : Set where
  field
    obstruction :
      StrictLogShapeObstruction

    obstructionSurface :
      String

    diagnostic :
      StrictLogDiagnosticNumbers

    blocksStrictPass :
      Bool

    blocksStrictPassIsTrue :
      blocksStrictPass ≡ true

    strictPassStillFalse :
      strictProtocolPass diagnostic ≡ false

    documentedWitness :
      List String

open StrictLogObstructionWitness public

canonicalSpan1LogPhiStarObstructionWitness :
  StrictLogObstructionWitness
canonicalSpan1LogPhiStarObstructionWitness =
  record
    { obstruction =
        span1LogPhiStar
    ; obstructionSurface =
        "span(1, log(phiStar)) log-linear component in the strict t43 residual"
    ; diagnostic =
        sigmaDashiV4StrictLogDiagnosticNumbers
    ; blocksStrictPass =
        true
    ; blocksStrictPassIsTrue =
        refl
    ; strictPassStillFalse =
        refl
    ; documentedWitness =
        "sigma_DASHI v4 strict-log diagnostic has log-linear subspace chi2 fraction 0.9687052128530349"
        ∷ "the named obstruction is the span of the intercept column 1 and the log(phiStar) slope column"
        ∷ "this witness documents why the current strict-log run is a shape-law target, not a strict pass receipt"
        ∷ "promotion requires an accepted orthogonalization/removal law and residual-complement bound"
        ∷ []
    }

canonicalSpan1LogPhiStarShapeObstructionDocumented :
  ShapeObstructionDocumented
canonicalSpan1LogPhiStarShapeObstructionDocumented =
  record
    { shapeObstruction =
        span1LogPhiStar
    ; obstructionDocumented =
        true
    ; obstructionDocumentedIsTrue =
        refl
    ; obstructionSummary =
        "strict-log failure is dominated by span(1, log(phiStar)), not by covariance inflation"
    ; nextOpenRequest =
        "derive a DASHI log-linear slope law for the below-Z phiStar spectrum and re-run the strict-log receipt"
    }

dyStrictLogTRBDThresholds :
  TRBD.TRBDProtocolThresholds
dyStrictLogTRBDThresholds =
  record
    { coverageThresholdName =
        "rho_min"
    ; coverageThreshold =
        "0.90"
    ; perpendicularThresholdName =
        "strict-log chi2/dof tau"
    ; perpendicularThreshold =
        "2.0"
    ; thresholdFrozen =
        true
    ; thresholdFrozenIsTrue =
        refl
    }

dyStrictLogSpan1LogPhiStarTypedBasis :
  TRBD.TypedBasis String
dyStrictLogSpan1LogPhiStarTypedBasis =
  record
    { basisName =
        "span1LogPhiStar"
    ; basisVectors =
        "1"
        ∷ "log(phiStar)"
        ∷ []
    ; basisSource =
        TRBD.structuralBasis
    ; notFitted =
        tt
    ; basisSourceDescription =
        "structural log-linear below-Z phiStar basis; fitted coefficients are diagnostic but the basis is not data-fitted"
    ; basisPromotionBoundary =
        "basis may type the obstruction, but fitted coefficients do not derive a DASHI shape law"
        ∷ "promotion requires a structural or causal derivation of the correction and a passing perpendicular residual"
        ∷ []
    }

canonicalDrellYanStrictLogTRBDReceipt :
  TRBD.TRBDReceipt String
canonicalDrellYanStrictLogTRBDReceipt =
  record
    { observed =
        "log sigma_data below-Z t43"
    ; predicted =
        "log sigma_DASHI_v4 below-Z t43"
    ; residualConvention =
        "log(prediction) - log(data)"
    ; metricOrCovariance =
        "inverse propagated log covariance, C_log[i,j] = C_raw[i,j] / (R_data[i] * R_data[j])"
    ; basis =
        dyStrictLogSpan1LogPhiStarTypedBasis
    ; basisCoefficients =
        "-0.3104937924536695"
        ∷ "-0.34242419691254444"
        ∷ []
    ; rawChi2PerDof =
        "3180.211733150705"
    ; perpendicularChi2PerDof =
        "111.96455543013676"
    ; basisCoverage =
        "0.968705212853035"
    ; basisCoverageFormula =
        "rho_B = 1 - (perpendicular chi2 / raw chi2)"
    ; coverageHonest =
        refl
    ; thresholds =
        dyStrictLogTRBDThresholds
    ; obstructionStatus =
        TRBD.obstructionTypedPartial "span1LogPhiStar"
    ; projectionArtifact =
        "scripts/data/outputs/dy_slope_decomposition_sigma_dashi_v4_20260515.json"
    ; diagnosticOnly =
        true
    ; promotionBoundary =
        "TRBD status is obstructionTypedPartial: coverage is high but perpendicular chi2/dof remains 111.96455543013676 > 2.0"
        ∷ "no PromotableTRBDReceipt is constructed for this DY strict-log receipt"
        ∷ []
    }

canonicalDrellYanStrictLogOpenShapeLawRequest :
  TRBD.OpenShapeLawRequest String
canonicalDrellYanStrictLogOpenShapeLawRequest =
  record
    { receipt =
        canonicalDrellYanStrictLogTRBDReceipt
    ; obstructionNamed =
        TRBD.openTypedPartial "span1LogPhiStar"
    ; derivationPending =
        record
          { requestedQuantity =
              "DASHI-derived below-Z log-linear phiStar slope correction"
          ; requestedDerivationSource =
              TRBD.structuralBasis
          ; requestOpen =
              true
          ; requestOpenIsTrue =
              refl
          ; requestNotes =
              "fitted correction slope is 0.3424241969125445, but a fitted coefficient is not a law"
              ∷ "single-slope removal is insufficient because perpendicular chi2/dof remains 111.96455543013676"
              ∷ []
          }
    ; nonPromoting =
        true
    ; nonPromotingIsTrue =
        refl
    ; notPromotableReason =
        "basis coverage is high, but TRBD classification is obstructionTypedPartial rather than obstructionTypedClean"
        ∷ "the residual complement still fails the strict threshold"
        ∷ []
    }

record DrellYanStrictLogLinearSubspaceReceipt : Setω where
  field
    scope :
      String

    phiStarDiagnostic :
      StrictLogDiagnosticNumbers

    sigmaDashiV4Diagnostic :
      StrictLogDiagnosticNumbers

    conjectureIStatus :
      StrictLogConjectureStatus

    conjectureIIStatus :
      StrictLogConjectureStatus

    conjectureIIIStatus :
      StrictLogConjectureStatus

    covarianceHelpsRatherThanInflates :
      Bool

    covarianceHelpsRatherThanInflatesIsTrue :
      covarianceHelpsRatherThanInflates ≡ true

    sigmaDashiV4FailureDominatedByLogLinearSubspace :
      Bool

    sigmaDashiV4FailureDominatedByLogLinearSubspaceIsTrue :
      sigmaDashiV4FailureDominatedByLogLinearSubspace ≡ true

    strictPassAchieved :
      Bool

    strictPassAchievedIsFalse :
      strictPassAchieved ≡ false

    correctedInterpretation :
      List String

    namedObstruction :
      StrictLogObstructionWitness

    nextTheoremTarget :
      String

    shapeObstruction :
      StrictLogShapeObstruction

    shapeObstructionDocumented :
      ShapeObstructionDocumented

    trbdReceipt :
      TRBD.TRBDReceipt String

    trbdOpenShapeLawRequest :
      TRBD.OpenShapeLawRequest String

    exactFirstMissing :
      List StrictLogFirstMissing

open DrellYanStrictLogLinearSubspaceReceipt public

canonicalDrellYanStrictLogLinearSubspaceReceipt :
  DrellYanStrictLogLinearSubspaceReceipt
canonicalDrellYanStrictLogLinearSubspaceReceipt =
  record
    { scope =
        "CMS-SMP-20-003 / HEPData ins2079374 t43 strict log-covariance diagnostics"
    ; phiStarDiagnostic =
        phiStarRatioStrictLogDiagnosticNumbers
    ; sigmaDashiV4Diagnostic =
        sigmaDashiV4StrictLogDiagnosticNumbers
    ; conjectureIStatus =
        empiricallyRefuted
    ; conjectureIIStatus =
        empiricallyRefuted
    ; conjectureIIIStatus =
        empiricallySupported
    ; covarianceHelpsRatherThanInflates =
        true
    ; covarianceHelpsRatherThanInflatesIsTrue =
        refl
    ; sigmaDashiV4FailureDominatedByLogLinearSubspace =
        true
    ; sigmaDashiV4FailureDominatedByLogLinearSubspaceIsTrue =
        refl
    ; strictPassAchieved =
        false
    ; strictPassAchievedIsFalse =
        refl
    ; correctedInterpretation =
        "full covariance reduces chi2 relative to diagonal-only covariance"
        ∷ "leading inverse-covariance modes are not rank-1 dominant"
        ∷ "the current sigma_DASHI v4 failure is dominated by the span of 1 and log(phiStar)"
        ∷ "strict pass requires removing the log-linear slope/intercept component and bounding the orthogonal complement"
        ∷ []
    ; namedObstruction =
        canonicalSpan1LogPhiStarObstructionWitness
    ; nextTheoremTarget =
        "StrictPassOrthogonalityObligation plus a depth-averaged curvature kernel candidate"
    ; shapeObstruction =
        span1LogPhiStar
    ; shapeObstructionDocumented =
        canonicalSpan1LogPhiStarShapeObstructionDocumented
    ; trbdReceipt =
        canonicalDrellYanStrictLogTRBDReceipt
    ; trbdOpenShapeLawRequest =
        canonicalDrellYanStrictLogOpenShapeLawRequest
    ; exactFirstMissing =
        missingDepthAveragedKernelImplementation
        ∷ missingSpan1LogPhiStarShapeLaw
        ∷ missingLogLinearOrthogonalityProof
        ∷ missingInterceptMatchProof
        ∷ missingResidualComplementBound
        ∷ missingStrictPassReceipt
        ∷ []
    }

canonicalDepthAveragedCurvatureCandidate :
  DepthAveragedCurvatureCandidate
canonicalDepthAveragedCurvatureCandidate =
  record
    { Depth =
        Nat
    ; PhiStar =
        Nat
    ; DepthMeasure =
        Nat
    ; depthAveragedKernel =
        λ _ _ _ _ → Nat
    ; analyticUniformDepthKernel =
        "(exp(-Lambda d_lo |log phi|) - exp(-Lambda d_hi |log phi|)) / (Lambda (d_hi - d_lo) |log phi|)"
    ; createsLogPhiCurvature =
        true
    ; createsLogPhiCurvatureIsTrue =
        refl
    ; promotionBoundary =
        "kernel candidate only; no strict chi2/dof <= 2 receipt is constructed"
        ∷ "depth bounds and depth measure must be frozen before comparison"
        ∷ "orthogonality to span(1, log(phiStar)) and residual complement bound remain missing"
        ∷ []
    }
