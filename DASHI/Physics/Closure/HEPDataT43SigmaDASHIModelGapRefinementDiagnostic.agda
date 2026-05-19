module DASHI.Physics.Closure.HEPDataT43SigmaDASHIModelGapRefinementDiagnostic where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Agda.Primitive using (Setω)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Physics.Closure.HEPDataT43DASHINativeComparisonDiagnostic as R38

------------------------------------------------------------------------
-- HEP-R39: sigma_DASHI model-gap refinement diagnostic.
--
-- HEP-R38 measured a dirty covariance-aware model gap:
--
--   chi2 / dof = 355674.6906162796
--
-- This is not a near-miss comparison failure.  It is a structural diagnostic
-- that the current finite-trit sigma_DASHI projection does not yet model the
-- t43 phi-star ratio observable.  HEP-R39 applies the v2 diagnostic
-- refinement and records the dirty covariance-aware result:
--
--   chi2 / dof = 68.41787311159007
--
-- This is real gap narrowing, but still far above the comparison-law
-- threshold and still dirty/synthetic-freeze.  It does not construct an
-- accepted comparison law, clean freeze receipt, empirical adequacy receipt,
-- or worker promotion receipt.

data HEPDataT43SigmaDASHIModelGapRefinementStatus : Set where
  dirtyHEPR38ModelGapNarrowedByV2ButStillBlocked :
    HEPDataT43SigmaDASHIModelGapRefinementStatus

data HEPDataT43SigmaDASHIModelGapSource : Set where
  fixedDepthCollapseGap :
    HEPDataT43SigmaDASHIModelGapSource
  physicalPhiStarEtaMappingGap :
    HEPDataT43SigmaDASHIModelGapSource
  missingBreitWignerZPeakMassNormalizationGap :
    HEPDataT43SigmaDASHIModelGapSource

canonicalHEPDataT43SigmaDASHIModelGapSources :
  List HEPDataT43SigmaDASHIModelGapSource
canonicalHEPDataT43SigmaDASHIModelGapSources =
  fixedDepthCollapseGap
  ∷ physicalPhiStarEtaMappingGap
  ∷ missingBreitWignerZPeakMassNormalizationGap
  ∷ []

data HEPDataT43SigmaDASHIV2RefinementObligation : Set where
  addPhiStarDependentCarrierDepth :
    HEPDataT43SigmaDASHIV2RefinementObligation
  replacePolarityHalfAngleAnalogyWithPhysicalPhiStarEtaMapping :
    HEPDataT43SigmaDASHIV2RefinementObligation
  addBreitWignerZPeakMassNormalization :
    HEPDataT43SigmaDASHIV2RefinementObligation
  keepObservedT43ValuesOutOfPredictionConstruction :
    HEPDataT43SigmaDASHIV2RefinementObligation
  rerunOnlyAfterCleanPredictionFreeze :
    HEPDataT43SigmaDASHIV2RefinementObligation
  requireFreshCovarianceAwareComparisonLawAfterProjection :
    HEPDataT43SigmaDASHIV2RefinementObligation

canonicalHEPDataT43SigmaDASHIV2RefinementObligations :
  List HEPDataT43SigmaDASHIV2RefinementObligation
canonicalHEPDataT43SigmaDASHIV2RefinementObligations =
  addPhiStarDependentCarrierDepth
  ∷ replacePolarityHalfAngleAnalogyWithPhysicalPhiStarEtaMapping
  ∷ addBreitWignerZPeakMassNormalization
  ∷ keepObservedT43ValuesOutOfPredictionConstruction
  ∷ rerunOnlyAfterCleanPredictionFreeze
  ∷ requireFreshCovarianceAwareComparisonLawAfterProjection
  ∷ []

data HEPDataT43SigmaDASHIModelGapRemainingBlocker : Set where
  cleanPredictionFixedAtStillMissing :
    HEPDataT43SigmaDASHIModelGapRemainingBlocker
  acceptedProjectionRunStillMissing :
    HEPDataT43SigmaDASHIModelGapRemainingBlocker
  acceptedComparisonLawStillUninhabited :
    HEPDataT43SigmaDASHIModelGapRemainingBlocker
  empiricalAdequacyStillUninhabited :
    HEPDataT43SigmaDASHIModelGapRemainingBlocker
  workerPromotionStillBlocked :
    HEPDataT43SigmaDASHIModelGapRemainingBlocker

canonicalHEPDataT43SigmaDASHIModelGapRemainingBlockers :
  List HEPDataT43SigmaDASHIModelGapRemainingBlocker
canonicalHEPDataT43SigmaDASHIModelGapRemainingBlockers =
  cleanPredictionFixedAtStillMissing
  ∷ acceptedProjectionRunStillMissing
  ∷ acceptedComparisonLawStillUninhabited
  ∷ empiricalAdequacyStillUninhabited
  ∷ workerPromotionStillBlocked
  ∷ []

data HEPDataT43SigmaDASHIModelGapBoundary : Set where
  v2ImplementationDiagnosticOnly :
    HEPDataT43SigmaDASHIModelGapBoundary
  noCleanFreezeHere :
    HEPDataT43SigmaDASHIModelGapBoundary
  noAcceptedProjectionRunHere :
    HEPDataT43SigmaDASHIModelGapBoundary
  noAcceptedComparisonLawHere :
    HEPDataT43SigmaDASHIModelGapBoundary
  noEmpiricalAdequacyHere :
    HEPDataT43SigmaDASHIModelGapBoundary
  noW3W4W5W8PromotionHere :
    HEPDataT43SigmaDASHIModelGapBoundary

canonicalHEPDataT43SigmaDASHIModelGapBoundaries :
  List HEPDataT43SigmaDASHIModelGapBoundary
canonicalHEPDataT43SigmaDASHIModelGapBoundaries =
  v2ImplementationDiagnosticOnly
  ∷ noCleanFreezeHere
  ∷ noAcceptedProjectionRunHere
  ∷ noAcceptedComparisonLawHere
  ∷ noEmpiricalAdequacyHere
  ∷ noW3W4W5W8PromotionHere
  ∷ []

data HEPDataT43R39AcceptedComparisonLawReceipt : Set where

hepR39AcceptedComparisonLawReceiptImpossibleHere :
  HEPDataT43R39AcceptedComparisonLawReceipt →
  ⊥
hepR39AcceptedComparisonLawReceiptImpossibleHere ()

data HEPDataT43R39PromotionReceipt : Set where

hepR39PromotionReceiptImpossibleHere :
  HEPDataT43R39PromotionReceipt →
  ⊥
hepR39PromotionReceiptImpossibleHere ()

record HEPDataT43SigmaDASHIModelGapRefinementDiagnostic : Setω where
  field
    status :
      HEPDataT43SigmaDASHIModelGapRefinementStatus

    upstreamComparisonDiagnostic :
      R38.HEPDataT43DASHINativeComparisonDiagnostic

    hepR38Chi2PerDofString :
      String

    hepR38Chi2PerDofIsCanonical :
      hepR38Chi2PerDofString
      ≡
      "355674.6906162796"

    hepR39DirtyProjectionArtifactPath :
      String

    hepR39DirtyProjectionArtifactPathIsCanonical :
      hepR39DirtyProjectionArtifactPath
      ≡
      "/tmp/t43_projection_hep_r39_dirty.json"

    hepR39DirtyProjectionFileSHA256 :
      String

    hepR39DirtyProjectionFileSHA256IsCanonical :
      hepR39DirtyProjectionFileSHA256
      ≡
      "8a11d0962d31ddb52b28256c5469174cf57fce23888f553923af1c21ba6a30ba"

    hepR39DirtyProjectionDigest :
      String

    hepR39DirtyProjectionDigestIsCanonical :
      hepR39DirtyProjectionDigest
      ≡
      "6c19f2eef039b494f8fddc42b8e0941e464adc8fc93e5502f4eadfd04cbc9c3b"

    hepR39DirtyFreezeHash :
      String

    hepR39DirtyFreezeHashIsCanonical :
      hepR39DirtyFreezeHash
      ≡
      "HEP-R39-dirty-diagnostic"

    hepR39Chi2String :
      String

    hepR39Chi2StringIsCanonical :
      hepR39Chi2String
      ≡
      "1231.5217160086213"

    hepR39DofString :
      String

    hepR39DofStringIsCanonical :
      hepR39DofString
      ≡
      "18"

    hepR39Chi2PerDofString :
      String

    hepR39Chi2PerDofStringIsCanonical :
      hepR39Chi2PerDofString
      ≡
      "68.41787311159007"

    hepR39ResidualRangeString :
      String

    hepR39ResidualRangeStringIsCanonical :
      hepR39ResidualRangeString
      ≡
      "-0.011206707061669437 to -0.0016013193462227626"

    hepR39FirstThreePullsString :
      String

    hepR39FirstThreePullsStringIsCanonical :
      hepR39FirstThreePullsString
      ≡
      "-20.058402887592976, -15.81554530871195, -9.732286913574525"

    v2RefinementRequired :
      Bool

    v2RefinementRequiredIsTrue :
      v2RefinementRequired ≡ true

    acceptedComparisonLawExistsHere :
      Bool

    acceptedComparisonLawExistsHereIsFalse :
      acceptedComparisonLawExistsHere ≡ false

    workerPromotionExistsHere :
      Bool

    workerPromotionExistsHereIsFalse :
      workerPromotionExistsHere ≡ false

    gapSources :
      List HEPDataT43SigmaDASHIModelGapSource

    gapSourcesAreCanonical :
      gapSources
      ≡
      canonicalHEPDataT43SigmaDASHIModelGapSources

    v2RefinementObligations :
      List HEPDataT43SigmaDASHIV2RefinementObligation

    v2RefinementObligationsAreCanonical :
      v2RefinementObligations
      ≡
      canonicalHEPDataT43SigmaDASHIV2RefinementObligations

    remainingBlockers :
      List HEPDataT43SigmaDASHIModelGapRemainingBlocker

    remainingBlockersAreCanonical :
      remainingBlockers
      ≡
      canonicalHEPDataT43SigmaDASHIModelGapRemainingBlockers

    boundaries :
      List HEPDataT43SigmaDASHIModelGapBoundary

    boundariesAreCanonical :
      boundaries
      ≡
      canonicalHEPDataT43SigmaDASHIModelGapBoundaries

    futureAcceptedComparisonLawBlocked :
      HEPDataT43R39AcceptedComparisonLawReceipt →
      ⊥

    futurePromotionBlocked :
      HEPDataT43R39PromotionReceipt →
      ⊥

canonicalHEPDataT43SigmaDASHIModelGapRefinementDiagnostic :
  HEPDataT43SigmaDASHIModelGapRefinementDiagnostic
canonicalHEPDataT43SigmaDASHIModelGapRefinementDiagnostic =
  record
    { status =
        dirtyHEPR38ModelGapNarrowedByV2ButStillBlocked
    ; upstreamComparisonDiagnostic =
        R38.canonicalHEPDataT43DASHINativeComparisonDiagnostic
    ; hepR38Chi2PerDofString =
        "355674.6906162796"
    ; hepR38Chi2PerDofIsCanonical =
        refl
    ; hepR39DirtyProjectionArtifactPath =
        "/tmp/t43_projection_hep_r39_dirty.json"
    ; hepR39DirtyProjectionArtifactPathIsCanonical =
        refl
    ; hepR39DirtyProjectionFileSHA256 =
        "8a11d0962d31ddb52b28256c5469174cf57fce23888f553923af1c21ba6a30ba"
    ; hepR39DirtyProjectionFileSHA256IsCanonical =
        refl
    ; hepR39DirtyProjectionDigest =
        "6c19f2eef039b494f8fddc42b8e0941e464adc8fc93e5502f4eadfd04cbc9c3b"
    ; hepR39DirtyProjectionDigestIsCanonical =
        refl
    ; hepR39DirtyFreezeHash =
        "HEP-R39-dirty-diagnostic"
    ; hepR39DirtyFreezeHashIsCanonical =
        refl
    ; hepR39Chi2String =
        "1231.5217160086213"
    ; hepR39Chi2StringIsCanonical =
        refl
    ; hepR39DofString =
        "18"
    ; hepR39DofStringIsCanonical =
        refl
    ; hepR39Chi2PerDofString =
        "68.41787311159007"
    ; hepR39Chi2PerDofStringIsCanonical =
        refl
    ; hepR39ResidualRangeString =
        "-0.011206707061669437 to -0.0016013193462227626"
    ; hepR39ResidualRangeStringIsCanonical =
        refl
    ; hepR39FirstThreePullsString =
        "-20.058402887592976, -15.81554530871195, -9.732286913574525"
    ; hepR39FirstThreePullsStringIsCanonical =
        refl
    ; v2RefinementRequired =
        true
    ; v2RefinementRequiredIsTrue =
        refl
    ; acceptedComparisonLawExistsHere =
        false
    ; acceptedComparisonLawExistsHereIsFalse =
        refl
    ; workerPromotionExistsHere =
        false
    ; workerPromotionExistsHereIsFalse =
        refl
    ; gapSources =
        canonicalHEPDataT43SigmaDASHIModelGapSources
    ; gapSourcesAreCanonical =
        refl
    ; v2RefinementObligations =
        canonicalHEPDataT43SigmaDASHIV2RefinementObligations
    ; v2RefinementObligationsAreCanonical =
        refl
    ; remainingBlockers =
        canonicalHEPDataT43SigmaDASHIModelGapRemainingBlockers
    ; remainingBlockersAreCanonical =
        refl
    ; boundaries =
        canonicalHEPDataT43SigmaDASHIModelGapBoundaries
    ; boundariesAreCanonical =
        refl
    ; futureAcceptedComparisonLawBlocked =
        hepR39AcceptedComparisonLawReceiptImpossibleHere
    ; futurePromotionBlocked =
        hepR39PromotionReceiptImpossibleHere
    }

canonicalHEPDataT43SigmaDASHIModelGapRefinementStatus :
  HEPDataT43SigmaDASHIModelGapRefinementStatus
canonicalHEPDataT43SigmaDASHIModelGapRefinementStatus =
  HEPDataT43SigmaDASHIModelGapRefinementDiagnostic.status
    canonicalHEPDataT43SigmaDASHIModelGapRefinementDiagnostic
