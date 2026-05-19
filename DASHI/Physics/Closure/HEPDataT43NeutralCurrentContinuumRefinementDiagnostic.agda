module DASHI.Physics.Closure.HEPDataT43NeutralCurrentContinuumRefinementDiagnostic where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Agda.Primitive using (Setω)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Physics.Closure.HEPDataT43SigmaDASHIModelGapRefinementDiagnostic as R39

------------------------------------------------------------------------
-- HEP-R40: neutral-current continuum refinement diagnostic.
--
-- HEP-R39 narrowed the dirty t43/t44 covariance-aware diagnostic to:
--
--   chi2 / dof = 68.41787311159007
--
-- HEP-R40 adds a bounded diagnostic gamma/Z neutral-current continuum factor
-- to the internal sigma_DASHI construction and reruns the dirty projection:
--
--   chi2 / dof = 28.65761549390974
--
-- This is another model-gap reduction only.  It is still synthetic-freeze,
-- dirty-worktree, and above the comparison-law threshold.  It does not
-- construct an accepted projection, comparison law, empirical adequacy
-- receipt, authority token, or W3/W4/W5/W8 promotion.

data HEPDataT43NeutralCurrentContinuumRefinementStatus : Set where
  dirtyHEPR39GapNarrowedByNeutralCurrentContinuumButStillBlocked :
    HEPDataT43NeutralCurrentContinuumRefinementStatus

data HEPDataT43NeutralCurrentContinuumRefinementField : Set where
  neutralCurrentContinuumFactor :
    HEPDataT43NeutralCurrentContinuumRefinementField
  softPhiStarSupport :
    HEPDataT43NeutralCurrentContinuumRefinementField
  shoulderPhiStarSupport :
    HEPDataT43NeutralCurrentContinuumRefinementField
  noObservedRatioSeeding :
    HEPDataT43NeutralCurrentContinuumRefinementField
  dirtyCovarianceDiagnostic :
    HEPDataT43NeutralCurrentContinuumRefinementField

canonicalHEPDataT43NeutralCurrentContinuumRefinementFields :
  List HEPDataT43NeutralCurrentContinuumRefinementField
canonicalHEPDataT43NeutralCurrentContinuumRefinementFields =
  neutralCurrentContinuumFactor
  ∷ softPhiStarSupport
  ∷ shoulderPhiStarSupport
  ∷ noObservedRatioSeeding
  ∷ dirtyCovarianceDiagnostic
  ∷ []

data HEPDataT43NeutralCurrentContinuumBoundary : Set where
  diagnosticContinuumOnly :
    HEPDataT43NeutralCurrentContinuumBoundary
  noCleanFreezeHere :
    HEPDataT43NeutralCurrentContinuumBoundary
  noAcceptedProjectionRunHere :
    HEPDataT43NeutralCurrentContinuumBoundary
  noAcceptedComparisonLawHere :
    HEPDataT43NeutralCurrentContinuumBoundary
  noEmpiricalAdequacyHere :
    HEPDataT43NeutralCurrentContinuumBoundary
  noW3W4W5W8PromotionHere :
    HEPDataT43NeutralCurrentContinuumBoundary

canonicalHEPDataT43NeutralCurrentContinuumBoundaries :
  List HEPDataT43NeutralCurrentContinuumBoundary
canonicalHEPDataT43NeutralCurrentContinuumBoundaries =
  diagnosticContinuumOnly
  ∷ noCleanFreezeHere
  ∷ noAcceptedProjectionRunHere
  ∷ noAcceptedComparisonLawHere
  ∷ noEmpiricalAdequacyHere
  ∷ noW3W4W5W8PromotionHere
  ∷ []

data HEPDataT43R40AcceptedComparisonLawReceipt : Set where

hepR40AcceptedComparisonLawReceiptImpossibleHere :
  HEPDataT43R40AcceptedComparisonLawReceipt →
  ⊥
hepR40AcceptedComparisonLawReceiptImpossibleHere ()

data HEPDataT43R40PromotionReceipt : Set where

hepR40PromotionReceiptImpossibleHere :
  HEPDataT43R40PromotionReceipt →
  ⊥
hepR40PromotionReceiptImpossibleHere ()

record HEPDataT43NeutralCurrentContinuumRefinementDiagnostic : Setω where
  field
    status :
      HEPDataT43NeutralCurrentContinuumRefinementStatus

    upstreamSigmaDASHIModelGapRefinement :
      R39.HEPDataT43SigmaDASHIModelGapRefinementDiagnostic

    hepR39Chi2PerDofString :
      String

    hepR39Chi2PerDofIsCanonical :
      hepR39Chi2PerDofString
      ≡
      "68.41787311159007"

    hepR40DirtyProjectionArtifactPath :
      String

    hepR40DirtyProjectionArtifactPathIsCanonical :
      hepR40DirtyProjectionArtifactPath
      ≡
      "/tmp/t43_projection_hep_r40_dirty.json"

    hepR40DirtyProjectionFileSHA256 :
      String

    hepR40DirtyProjectionFileSHA256IsCanonical :
      hepR40DirtyProjectionFileSHA256
      ≡
      "7772bad5b8bdc7407b6432d8fe7585fb7ed357f6eed3db4e3d6883c9c1cffac6"

    hepR40DirtyProjectionDigest :
      String

    hepR40DirtyProjectionDigestIsCanonical :
      hepR40DirtyProjectionDigest
      ≡
      "96be51a8019b7fcd88e36def0d61fd483c9b3bfe4a1698c9cce6079188567ff9"

    hepR40DirtyFreezeHash :
      String

    hepR40DirtyFreezeHashIsCanonical :
      hepR40DirtyFreezeHash
      ≡
      "HEP-R40-dirty-diagnostic"

    hepR40Chi2String :
      String

    hepR40Chi2StringIsCanonical :
      hepR40Chi2String
      ≡
      "515.8370788903753"

    hepR40DofString :
      String

    hepR40DofStringIsCanonical :
      hepR40DofString
      ≡
      "18"

    hepR40Chi2PerDofString :
      String

    hepR40Chi2PerDofStringIsCanonical :
      hepR40Chi2PerDofString
      ≡
      "28.65761549390974"

    hepR40ResidualRangeString :
      String

    hepR40ResidualRangeStringIsCanonical :
      hepR40ResidualRangeString
      ≡
      "-0.002095752548174956 to 0.003318827386338624"

    hepR40FirstThreePullsString :
      String

    hepR40FirstThreePullsStringIsCanonical :
      hepR40FirstThreePullsString
      ≡
      "-0.3942458219739305, -1.457261191185934, -1.0453450331655705"

    acceptedComparisonLawExistsHere :
      Bool

    acceptedComparisonLawExistsHereIsFalse :
      acceptedComparisonLawExistsHere ≡ false

    workerPromotionExistsHere :
      Bool

    workerPromotionExistsHereIsFalse :
      workerPromotionExistsHere ≡ false

    refinementFields :
      List HEPDataT43NeutralCurrentContinuumRefinementField

    refinementFieldsAreCanonical :
      refinementFields
      ≡
      canonicalHEPDataT43NeutralCurrentContinuumRefinementFields

    boundaries :
      List HEPDataT43NeutralCurrentContinuumBoundary

    boundariesAreCanonical :
      boundaries
      ≡
      canonicalHEPDataT43NeutralCurrentContinuumBoundaries

    futureAcceptedComparisonLawBlocked :
      HEPDataT43R40AcceptedComparisonLawReceipt →
      ⊥

    futurePromotionBlocked :
      HEPDataT43R40PromotionReceipt →
      ⊥

canonicalHEPDataT43NeutralCurrentContinuumRefinementDiagnostic :
  HEPDataT43NeutralCurrentContinuumRefinementDiagnostic
canonicalHEPDataT43NeutralCurrentContinuumRefinementDiagnostic =
  record
    { status =
        dirtyHEPR39GapNarrowedByNeutralCurrentContinuumButStillBlocked
    ; upstreamSigmaDASHIModelGapRefinement =
        R39.canonicalHEPDataT43SigmaDASHIModelGapRefinementDiagnostic
    ; hepR39Chi2PerDofString =
        "68.41787311159007"
    ; hepR39Chi2PerDofIsCanonical =
        refl
    ; hepR40DirtyProjectionArtifactPath =
        "/tmp/t43_projection_hep_r40_dirty.json"
    ; hepR40DirtyProjectionArtifactPathIsCanonical =
        refl
    ; hepR40DirtyProjectionFileSHA256 =
        "7772bad5b8bdc7407b6432d8fe7585fb7ed357f6eed3db4e3d6883c9c1cffac6"
    ; hepR40DirtyProjectionFileSHA256IsCanonical =
        refl
    ; hepR40DirtyProjectionDigest =
        "96be51a8019b7fcd88e36def0d61fd483c9b3bfe4a1698c9cce6079188567ff9"
    ; hepR40DirtyProjectionDigestIsCanonical =
        refl
    ; hepR40DirtyFreezeHash =
        "HEP-R40-dirty-diagnostic"
    ; hepR40DirtyFreezeHashIsCanonical =
        refl
    ; hepR40Chi2String =
        "515.8370788903753"
    ; hepR40Chi2StringIsCanonical =
        refl
    ; hepR40DofString =
        "18"
    ; hepR40DofStringIsCanonical =
        refl
    ; hepR40Chi2PerDofString =
        "28.65761549390974"
    ; hepR40Chi2PerDofStringIsCanonical =
        refl
    ; hepR40ResidualRangeString =
        "-0.002095752548174956 to 0.003318827386338624"
    ; hepR40ResidualRangeStringIsCanonical =
        refl
    ; hepR40FirstThreePullsString =
        "-0.3942458219739305, -1.457261191185934, -1.0453450331655705"
    ; hepR40FirstThreePullsStringIsCanonical =
        refl
    ; acceptedComparisonLawExistsHere =
        false
    ; acceptedComparisonLawExistsHereIsFalse =
        refl
    ; workerPromotionExistsHere =
        false
    ; workerPromotionExistsHereIsFalse =
        refl
    ; refinementFields =
        canonicalHEPDataT43NeutralCurrentContinuumRefinementFields
    ; refinementFieldsAreCanonical =
        refl
    ; boundaries =
        canonicalHEPDataT43NeutralCurrentContinuumBoundaries
    ; boundariesAreCanonical =
        refl
    ; futureAcceptedComparisonLawBlocked =
        hepR40AcceptedComparisonLawReceiptImpossibleHere
    ; futurePromotionBlocked =
        hepR40PromotionReceiptImpossibleHere
    }

canonicalHEPDataT43NeutralCurrentContinuumRefinementStatus :
  HEPDataT43NeutralCurrentContinuumRefinementStatus
canonicalHEPDataT43NeutralCurrentContinuumRefinementStatus =
  HEPDataT43NeutralCurrentContinuumRefinementDiagnostic.status
    canonicalHEPDataT43NeutralCurrentContinuumRefinementDiagnostic
