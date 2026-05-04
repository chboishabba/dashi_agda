module DASHI.Physics.Closure.HEPDataT43PosteriorShapeResponseDiagnostic where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Agda.Primitive using (Setω)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Physics.Closure.HEPDataT43NeutralCurrentContinuumRefinementDiagnostic as R40

------------------------------------------------------------------------
-- HEP-R41: posterior shape-response diagnostic.
--
-- HEP-R40 narrowed the dirty t43/t44 covariance-aware diagnostic to:
--
--   chi2 / dof = 28.65761549390974
--
-- HEP-R41 adds a posterior shoulder-dip / recovery-bump response after
-- inspecting the HEP-R40 residual shape.  The dirty diagnostic then reaches:
--
--   chi2 / dof = 1.7408778006026118
--
-- Numerically this is below the future threshold, but it is not an accepted
-- comparison law: the response was selected after observing the residuals,
-- the freeze hash is synthetic, the worktree is dirty, and no authority or
-- pre-registration receipt exists.  This module records a numeric-pass /
-- governance-fail diagnostic only.

data HEPDataT43PosteriorShapeResponseStatus : Set where
  dirtyNumericThresholdMetButGovernanceBlocked :
    HEPDataT43PosteriorShapeResponseStatus

data HEPDataT43PosteriorShapeResponseField : Set where
  shoulderDipResponse :
    HEPDataT43PosteriorShapeResponseField
  recoveryBumpResponse :
    HEPDataT43PosteriorShapeResponseField
  posteriorResidualInspection :
    HEPDataT43PosteriorShapeResponseField
  dirtyCovarianceDiagnostic :
    HEPDataT43PosteriorShapeResponseField
  numericPassGovernanceFail :
    HEPDataT43PosteriorShapeResponseField

canonicalHEPDataT43PosteriorShapeResponseFields :
  List HEPDataT43PosteriorShapeResponseField
canonicalHEPDataT43PosteriorShapeResponseFields =
  shoulderDipResponse
  ∷ recoveryBumpResponse
  ∷ posteriorResidualInspection
  ∷ dirtyCovarianceDiagnostic
  ∷ numericPassGovernanceFail
  ∷ []

data HEPDataT43PosteriorShapeResponseBoundary : Set where
  posteriorDiagnosticOnly :
    HEPDataT43PosteriorShapeResponseBoundary
  noCleanFreezeHere :
    HEPDataT43PosteriorShapeResponseBoundary
  noPreRegisteredPredictionHere :
    HEPDataT43PosteriorShapeResponseBoundary
  noAcceptedComparisonLawHere :
    HEPDataT43PosteriorShapeResponseBoundary
  noEmpiricalAdequacyHere :
    HEPDataT43PosteriorShapeResponseBoundary
  noW3W4W5W8PromotionHere :
    HEPDataT43PosteriorShapeResponseBoundary

canonicalHEPDataT43PosteriorShapeResponseBoundaries :
  List HEPDataT43PosteriorShapeResponseBoundary
canonicalHEPDataT43PosteriorShapeResponseBoundaries =
  posteriorDiagnosticOnly
  ∷ noCleanFreezeHere
  ∷ noPreRegisteredPredictionHere
  ∷ noAcceptedComparisonLawHere
  ∷ noEmpiricalAdequacyHere
  ∷ noW3W4W5W8PromotionHere
  ∷ []

data HEPDataT43R41AcceptedComparisonLawReceipt : Set where

hepR41AcceptedComparisonLawReceiptImpossibleHere :
  HEPDataT43R41AcceptedComparisonLawReceipt →
  ⊥
hepR41AcceptedComparisonLawReceiptImpossibleHere ()

data HEPDataT43R41PromotionReceipt : Set where

hepR41PromotionReceiptImpossibleHere :
  HEPDataT43R41PromotionReceipt →
  ⊥
hepR41PromotionReceiptImpossibleHere ()

record HEPDataT43PosteriorShapeResponseDiagnostic : Setω where
  field
    status :
      HEPDataT43PosteriorShapeResponseStatus

    upstreamNeutralCurrentContinuumDiagnostic :
      R40.HEPDataT43NeutralCurrentContinuumRefinementDiagnostic

    hepR40Chi2PerDofString :
      String

    hepR40Chi2PerDofIsCanonical :
      hepR40Chi2PerDofString
      ≡
      "28.65761549390974"

    hepR41DirtyProjectionArtifactPath :
      String

    hepR41DirtyProjectionArtifactPathIsCanonical :
      hepR41DirtyProjectionArtifactPath
      ≡
      "/tmp/t43_projection_hep_r41_dirty.json"

    hepR41DirtyProjectionFileSHA256 :
      String

    hepR41DirtyProjectionFileSHA256IsCanonical :
      hepR41DirtyProjectionFileSHA256
      ≡
      "61bdfa327ee79a8979fe28c932ddf3f39052adc23aa94ef9b070c9ccfcafc905"

    hepR41DirtyProjectionDigest :
      String

    hepR41DirtyProjectionDigestIsCanonical :
      hepR41DirtyProjectionDigest
      ≡
      "4f131476a22ea8b9315370378f106e19c044964335f0b4a1a7d6e846e90ee336"

    hepR41DirtyFreezeHash :
      String

    hepR41DirtyFreezeHashIsCanonical :
      hepR41DirtyFreezeHash
      ≡
      "HEP-R41-dirty-diagnostic"

    hepR41Chi2String :
      String

    hepR41Chi2StringIsCanonical :
      hepR41Chi2String
      ≡
      "31.33580041084701"

    hepR41DofString :
      String

    hepR41DofStringIsCanonical :
      hepR41DofString
      ≡
      "18"

    hepR41Chi2PerDofString :
      String

    hepR41Chi2PerDofStringIsCanonical :
      hepR41Chi2PerDofString
      ≡
      "1.7408778006026118"

    hepR41ResidualRangeString :
      String

    hepR41ResidualRangeStringIsCanonical :
      hepR41ResidualRangeString
      ≡
      "-0.0010955170766824007 to 0.0005772369356618623"

    hepR41FirstThreePullsString :
      String

    hepR41FirstThreePullsStringIsCanonical :
      hepR41FirstThreePullsString
      ≡
      "-0.3942354635434069, -1.4566769302829727, -1.0401784201446023"

    numericThresholdMet :
      Bool

    numericThresholdMetIsTrue :
      numericThresholdMet ≡ true

    acceptedComparisonLawExistsHere :
      Bool

    acceptedComparisonLawExistsHereIsFalse :
      acceptedComparisonLawExistsHere ≡ false

    workerPromotionExistsHere :
      Bool

    workerPromotionExistsHereIsFalse :
      workerPromotionExistsHere ≡ false

    responseFields :
      List HEPDataT43PosteriorShapeResponseField

    responseFieldsAreCanonical :
      responseFields
      ≡
      canonicalHEPDataT43PosteriorShapeResponseFields

    boundaries :
      List HEPDataT43PosteriorShapeResponseBoundary

    boundariesAreCanonical :
      boundaries
      ≡
      canonicalHEPDataT43PosteriorShapeResponseBoundaries

    futureAcceptedComparisonLawBlocked :
      HEPDataT43R41AcceptedComparisonLawReceipt →
      ⊥

    futurePromotionBlocked :
      HEPDataT43R41PromotionReceipt →
      ⊥

canonicalHEPDataT43PosteriorShapeResponseDiagnostic :
  HEPDataT43PosteriorShapeResponseDiagnostic
canonicalHEPDataT43PosteriorShapeResponseDiagnostic =
  record
    { status =
        dirtyNumericThresholdMetButGovernanceBlocked
    ; upstreamNeutralCurrentContinuumDiagnostic =
        R40.canonicalHEPDataT43NeutralCurrentContinuumRefinementDiagnostic
    ; hepR40Chi2PerDofString =
        "28.65761549390974"
    ; hepR40Chi2PerDofIsCanonical =
        refl
    ; hepR41DirtyProjectionArtifactPath =
        "/tmp/t43_projection_hep_r41_dirty.json"
    ; hepR41DirtyProjectionArtifactPathIsCanonical =
        refl
    ; hepR41DirtyProjectionFileSHA256 =
        "61bdfa327ee79a8979fe28c932ddf3f39052adc23aa94ef9b070c9ccfcafc905"
    ; hepR41DirtyProjectionFileSHA256IsCanonical =
        refl
    ; hepR41DirtyProjectionDigest =
        "4f131476a22ea8b9315370378f106e19c044964335f0b4a1a7d6e846e90ee336"
    ; hepR41DirtyProjectionDigestIsCanonical =
        refl
    ; hepR41DirtyFreezeHash =
        "HEP-R41-dirty-diagnostic"
    ; hepR41DirtyFreezeHashIsCanonical =
        refl
    ; hepR41Chi2String =
        "31.33580041084701"
    ; hepR41Chi2StringIsCanonical =
        refl
    ; hepR41DofString =
        "18"
    ; hepR41DofStringIsCanonical =
        refl
    ; hepR41Chi2PerDofString =
        "1.7408778006026118"
    ; hepR41Chi2PerDofStringIsCanonical =
        refl
    ; hepR41ResidualRangeString =
        "-0.0010955170766824007 to 0.0005772369356618623"
    ; hepR41ResidualRangeStringIsCanonical =
        refl
    ; hepR41FirstThreePullsString =
        "-0.3942354635434069, -1.4566769302829727, -1.0401784201446023"
    ; hepR41FirstThreePullsStringIsCanonical =
        refl
    ; numericThresholdMet =
        true
    ; numericThresholdMetIsTrue =
        refl
    ; acceptedComparisonLawExistsHere =
        false
    ; acceptedComparisonLawExistsHereIsFalse =
        refl
    ; workerPromotionExistsHere =
        false
    ; workerPromotionExistsHereIsFalse =
        refl
    ; responseFields =
        canonicalHEPDataT43PosteriorShapeResponseFields
    ; responseFieldsAreCanonical =
        refl
    ; boundaries =
        canonicalHEPDataT43PosteriorShapeResponseBoundaries
    ; boundariesAreCanonical =
        refl
    ; futureAcceptedComparisonLawBlocked =
        hepR41AcceptedComparisonLawReceiptImpossibleHere
    ; futurePromotionBlocked =
        hepR41PromotionReceiptImpossibleHere
    }

canonicalHEPDataT43PosteriorShapeResponseStatus :
  HEPDataT43PosteriorShapeResponseStatus
canonicalHEPDataT43PosteriorShapeResponseStatus =
  HEPDataT43PosteriorShapeResponseDiagnostic.status
    canonicalHEPDataT43PosteriorShapeResponseDiagnostic
