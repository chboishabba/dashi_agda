module DASHI.Physics.Closure.HEPDataT45HoldoutValidationDiagnostic where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Agda.Primitive using (Setω)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Physics.Closure.HEPDataT43PosteriorShapeResponseDiagnostic as R41

------------------------------------------------------------------------
-- HEP-R42: t45/t46 independent holdout validation diagnostic.
--
-- HEP-R41 reached a dirty t43 numeric threshold:
--
--   t43 chi2 / dof = 1.7408778006026118
--
-- HEP-R42 freezes that posterior diagnostic model unchanged and tests it on
-- the independent same-record ratio table:
--
--   t45 = phistar mass 106-170 over mass 76-106
--   t46 = covariance matrices for t45
--
-- The holdout dirty result is:
--
--   t45 chi2 / dof = 222.54402462995546
--
-- This proves the HEP-R41 numeric pass is not a general empirical adequacy
-- receipt.  The model underpredicts every t45 bin, so the next admissible move
-- is a mass-window-general prediction law, not W3 promotion.

data HEPDataT45HoldoutValidationStatus : Set where
  unchangedHEPR41ModelFailsT45Holdout :
    HEPDataT45HoldoutValidationStatus

data HEPDataT45HoldoutValidationField : Set where
  holdoutRatioTableT45 :
    HEPDataT45HoldoutValidationField
  holdoutCovarianceTableT46 :
    HEPDataT45HoldoutValidationField
  unchangedPosteriorModel :
    HEPDataT45HoldoutValidationField
  allBinsUnderpredicted :
    HEPDataT45HoldoutValidationField
  noGeneralEmpiricalAdequacy :
    HEPDataT45HoldoutValidationField

canonicalHEPDataT45HoldoutValidationFields :
  List HEPDataT45HoldoutValidationField
canonicalHEPDataT45HoldoutValidationFields =
  holdoutRatioTableT45
  ∷ holdoutCovarianceTableT46
  ∷ unchangedPosteriorModel
  ∷ allBinsUnderpredicted
  ∷ noGeneralEmpiricalAdequacy
  ∷ []

data HEPDataT45HoldoutValidationBoundary : Set where
  holdoutFailureDiagnosticOnly :
    HEPDataT45HoldoutValidationBoundary
  noCleanFreezeHere :
    HEPDataT45HoldoutValidationBoundary
  noAcceptedComparisonLawHere :
    HEPDataT45HoldoutValidationBoundary
  noGeneralPredictionReceiptHere :
    HEPDataT45HoldoutValidationBoundary
  noEmpiricalAdequacyHere :
    HEPDataT45HoldoutValidationBoundary
  noW3W4W5W8PromotionHere :
    HEPDataT45HoldoutValidationBoundary

canonicalHEPDataT45HoldoutValidationBoundaries :
  List HEPDataT45HoldoutValidationBoundary
canonicalHEPDataT45HoldoutValidationBoundaries =
  holdoutFailureDiagnosticOnly
  ∷ noCleanFreezeHere
  ∷ noAcceptedComparisonLawHere
  ∷ noGeneralPredictionReceiptHere
  ∷ noEmpiricalAdequacyHere
  ∷ noW3W4W5W8PromotionHere
  ∷ []

data HEPDataT45AcceptedHoldoutReceipt : Set where

hepR42AcceptedHoldoutReceiptImpossibleHere :
  HEPDataT45AcceptedHoldoutReceipt →
  ⊥
hepR42AcceptedHoldoutReceiptImpossibleHere ()

data HEPDataT45PromotionReceipt : Set where

hepR42PromotionReceiptImpossibleHere :
  HEPDataT45PromotionReceipt →
  ⊥
hepR42PromotionReceiptImpossibleHere ()

record HEPDataT45HoldoutValidationDiagnostic : Setω where
  field
    status :
      HEPDataT45HoldoutValidationStatus

    upstreamPosteriorShapeResponseDiagnostic :
      R41.HEPDataT43PosteriorShapeResponseDiagnostic

    hepR41T43Chi2PerDofString :
      String

    hepR41T43Chi2PerDofIsCanonical :
      hepR41T43Chi2PerDofString
      ≡
      "1.7408778006026118"

    t45Digest :
      String

    t45DigestIsCanonical :
      t45Digest
      ≡
      "bcc1450c5c7818e2792f06f1882c6facdea2e4079070b777f2c5ac3b87343433"

    t46Digest :
      String

    t46DigestIsCanonical :
      t46Digest
      ≡
      "e325d82ec3ba6962042c54f6b98a911d456f9bf00db22d2238b0cd76e71dcb3f"

    hepR42DirtyProjectionArtifactPath :
      String

    hepR42DirtyProjectionArtifactPathIsCanonical :
      hepR42DirtyProjectionArtifactPath
      ≡
      "/tmp/t45_projection_hep_r42_holdout_dirty.json"

    hepR42DirtyProjectionFileSHA256 :
      String

    hepR42DirtyProjectionFileSHA256IsCanonical :
      hepR42DirtyProjectionFileSHA256
      ≡
      "60242829cd37a9508c1b21da969c43383c1e00f6e4b6c77457ee5d1a67e2b4e3"

    hepR42DirtyProjectionDigest :
      String

    hepR42DirtyProjectionDigestIsCanonical :
      hepR42DirtyProjectionDigest
      ≡
      "2ac58b6d7c16384769dae42be2877c0025797acacc730f9d9443b00e538bda25"

    hepR42DirtyFreezeHash :
      String

    hepR42DirtyFreezeHashIsCanonical :
      hepR42DirtyFreezeHash
      ≡
      "HEP-R42-holdout-dirty-diagnostic"

    hepR42Chi2String :
      String

    hepR42Chi2StringIsCanonical :
      hepR42Chi2String
      ≡
      "4005.792443339198"

    hepR42DofString :
      String

    hepR42DofStringIsCanonical :
      hepR42DofString
      ≡
      "18"

    hepR42Chi2PerDofString :
      String

    hepR42Chi2PerDofStringIsCanonical :
      hepR42Chi2PerDofString
      ≡
      "222.54402462995546"

    hepR42ResidualRangeString :
      String

    hepR42ResidualRangeStringIsCanonical :
      hepR42ResidualRangeString
      ≡
      "-0.016478603959446673 to -0.014765036132624995"

    hepR42FirstThreePullsString :
      String

    hepR42FirstThreePullsStringIsCanonical :
      hepR42FirstThreePullsString
      ≡
      "-40.29294654782936, -44.9233638377081, -46.511886099538266"

    t43NumericThresholdMetButHoldoutFails :
      Bool

    t43NumericThresholdMetButHoldoutFailsIsTrue :
      t43NumericThresholdMetButHoldoutFails ≡ true

    acceptedHoldoutReceiptExistsHere :
      Bool

    acceptedHoldoutReceiptExistsHereIsFalse :
      acceptedHoldoutReceiptExistsHere ≡ false

    workerPromotionExistsHere :
      Bool

    workerPromotionExistsHereIsFalse :
      workerPromotionExistsHere ≡ false

    validationFields :
      List HEPDataT45HoldoutValidationField

    validationFieldsAreCanonical :
      validationFields
      ≡
      canonicalHEPDataT45HoldoutValidationFields

    boundaries :
      List HEPDataT45HoldoutValidationBoundary

    boundariesAreCanonical :
      boundaries
      ≡
      canonicalHEPDataT45HoldoutValidationBoundaries

    futureAcceptedHoldoutReceiptBlocked :
      HEPDataT45AcceptedHoldoutReceipt →
      ⊥

    futurePromotionBlocked :
      HEPDataT45PromotionReceipt →
      ⊥

canonicalHEPDataT45HoldoutValidationDiagnostic :
  HEPDataT45HoldoutValidationDiagnostic
canonicalHEPDataT45HoldoutValidationDiagnostic =
  record
    { status =
        unchangedHEPR41ModelFailsT45Holdout
    ; upstreamPosteriorShapeResponseDiagnostic =
        R41.canonicalHEPDataT43PosteriorShapeResponseDiagnostic
    ; hepR41T43Chi2PerDofString =
        "1.7408778006026118"
    ; hepR41T43Chi2PerDofIsCanonical =
        refl
    ; t45Digest =
        "bcc1450c5c7818e2792f06f1882c6facdea2e4079070b777f2c5ac3b87343433"
    ; t45DigestIsCanonical =
        refl
    ; t46Digest =
        "e325d82ec3ba6962042c54f6b98a911d456f9bf00db22d2238b0cd76e71dcb3f"
    ; t46DigestIsCanonical =
        refl
    ; hepR42DirtyProjectionArtifactPath =
        "/tmp/t45_projection_hep_r42_holdout_dirty.json"
    ; hepR42DirtyProjectionArtifactPathIsCanonical =
        refl
    ; hepR42DirtyProjectionFileSHA256 =
        "60242829cd37a9508c1b21da969c43383c1e00f6e4b6c77457ee5d1a67e2b4e3"
    ; hepR42DirtyProjectionFileSHA256IsCanonical =
        refl
    ; hepR42DirtyProjectionDigest =
        "2ac58b6d7c16384769dae42be2877c0025797acacc730f9d9443b00e538bda25"
    ; hepR42DirtyProjectionDigestIsCanonical =
        refl
    ; hepR42DirtyFreezeHash =
        "HEP-R42-holdout-dirty-diagnostic"
    ; hepR42DirtyFreezeHashIsCanonical =
        refl
    ; hepR42Chi2String =
        "4005.792443339198"
    ; hepR42Chi2StringIsCanonical =
        refl
    ; hepR42DofString =
        "18"
    ; hepR42DofStringIsCanonical =
        refl
    ; hepR42Chi2PerDofString =
        "222.54402462995546"
    ; hepR42Chi2PerDofStringIsCanonical =
        refl
    ; hepR42ResidualRangeString =
        "-0.016478603959446673 to -0.014765036132624995"
    ; hepR42ResidualRangeStringIsCanonical =
        refl
    ; hepR42FirstThreePullsString =
        "-40.29294654782936, -44.9233638377081, -46.511886099538266"
    ; hepR42FirstThreePullsStringIsCanonical =
        refl
    ; t43NumericThresholdMetButHoldoutFails =
        true
    ; t43NumericThresholdMetButHoldoutFailsIsTrue =
        refl
    ; acceptedHoldoutReceiptExistsHere =
        false
    ; acceptedHoldoutReceiptExistsHereIsFalse =
        refl
    ; workerPromotionExistsHere =
        false
    ; workerPromotionExistsHereIsFalse =
        refl
    ; validationFields =
        canonicalHEPDataT45HoldoutValidationFields
    ; validationFieldsAreCanonical =
        refl
    ; boundaries =
        canonicalHEPDataT45HoldoutValidationBoundaries
    ; boundariesAreCanonical =
        refl
    ; futureAcceptedHoldoutReceiptBlocked =
        hepR42AcceptedHoldoutReceiptImpossibleHere
    ; futurePromotionBlocked =
        hepR42PromotionReceiptImpossibleHere
    }

canonicalHEPDataT45HoldoutValidationStatus :
  HEPDataT45HoldoutValidationStatus
canonicalHEPDataT45HoldoutValidationStatus =
  HEPDataT45HoldoutValidationDiagnostic.status
    canonicalHEPDataT45HoldoutValidationDiagnostic
