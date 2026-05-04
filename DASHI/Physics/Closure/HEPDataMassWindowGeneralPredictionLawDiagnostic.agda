module DASHI.Physics.Closure.HEPDataMassWindowGeneralPredictionLawDiagnostic where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Agda.Primitive using (Setω)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Physics.Closure.HEPDataT43PosteriorShapeResponseDiagnostic as R41
import DASHI.Physics.Closure.HEPDataT45HoldoutValidationDiagnostic as R42

------------------------------------------------------------------------
-- HEP-R43: mass-window-general prediction law diagnostic.
--
-- HEP-R41 records a t43 posterior diagnostic that numerically passes:
--
--   t43 chi2 / dof = 1.7408778006026118
--
-- It is not promoted because the response was tuned after inspecting t43
-- residuals.  HEP-R42 applied that unchanged posterior model to the independent
-- t45/t46 ratio holdout and failed:
--
--   t45 chi2 / dof = 222.54402462995546
--
-- The holdout failure proves that the t43 posterior numeric pass is not a
-- mass-window-general empirical adequacy receipt.  HEP-R43 therefore requires
-- a law that predicts both 50-76 / 76-106 and 106-170 / 76-106 without
-- observed-table tuning.  Table t44 is only the covariance companion for t43,
-- not an independent validation ratio.

data HEPDataMassWindowGeneralPredictionLawStatus : Set where
  massWindowGeneralLawRequiredAfterT45HoldoutFailure :
    HEPDataMassWindowGeneralPredictionLawStatus

data HEPDataMassWindowGeneralPredictionLawField : Set where
  t43PosteriorNumericPass :
    HEPDataMassWindowGeneralPredictionLawField
  t43NoPromotionAfterResidualInspection :
    HEPDataMassWindowGeneralPredictionLawField
  t45IndependentHoldoutFailure :
    HEPDataMassWindowGeneralPredictionLawField
  t44CovarianceCompanionOnly :
    HEPDataMassWindowGeneralPredictionLawField
  lawMustProduceLowMassOverZPeak :
    HEPDataMassWindowGeneralPredictionLawField
  lawMustProduceHighMassOverZPeak :
    HEPDataMassWindowGeneralPredictionLawField
  noObservedTableTuning :
    HEPDataMassWindowGeneralPredictionLawField

canonicalHEPDataMassWindowGeneralPredictionLawFields :
  List HEPDataMassWindowGeneralPredictionLawField
canonicalHEPDataMassWindowGeneralPredictionLawFields =
  t43PosteriorNumericPass
  ∷ t43NoPromotionAfterResidualInspection
  ∷ t45IndependentHoldoutFailure
  ∷ t44CovarianceCompanionOnly
  ∷ lawMustProduceLowMassOverZPeak
  ∷ lawMustProduceHighMassOverZPeak
  ∷ noObservedTableTuning
  ∷ []

data HEPDataMassWindowGeneralPredictionLawBoundary : Set where
  diagnosticObligationOnly :
    HEPDataMassWindowGeneralPredictionLawBoundary
  noAcceptedGeneralLawHere :
    HEPDataMassWindowGeneralPredictionLawBoundary
  noCleanFreezeHere :
    HEPDataMassWindowGeneralPredictionLawBoundary
  noAdditionalHoldoutHere :
    HEPDataMassWindowGeneralPredictionLawBoundary
  noW3PromotionHere :
    HEPDataMassWindowGeneralPredictionLawBoundary

canonicalHEPDataMassWindowGeneralPredictionLawBoundaries :
  List HEPDataMassWindowGeneralPredictionLawBoundary
canonicalHEPDataMassWindowGeneralPredictionLawBoundaries =
  diagnosticObligationOnly
  ∷ noAcceptedGeneralLawHere
  ∷ noCleanFreezeHere
  ∷ noAdditionalHoldoutHere
  ∷ noW3PromotionHere
  ∷ []

data HEPDataMassWindowGeneralPredictionLawGovernanceMarker : Set where
  NonPromoting :
    HEPDataMassWindowGeneralPredictionLawGovernanceMarker
  W3Blocked :
    HEPDataMassWindowGeneralPredictionLawGovernanceMarker
  CleanFreezeRequired :
    HEPDataMassWindowGeneralPredictionLawGovernanceMarker
  AdditionalHoldoutRequired :
    HEPDataMassWindowGeneralPredictionLawGovernanceMarker

canonicalHEPDataMassWindowGeneralPredictionLawGovernanceMarkers :
  List HEPDataMassWindowGeneralPredictionLawGovernanceMarker
canonicalHEPDataMassWindowGeneralPredictionLawGovernanceMarkers =
  NonPromoting
  ∷ W3Blocked
  ∷ CleanFreezeRequired
  ∷ AdditionalHoldoutRequired
  ∷ []

data HEPDataMassWindowGeneralLawReceipt : Set where

hepR43AcceptedGeneralLawReceiptImpossibleHere :
  HEPDataMassWindowGeneralLawReceipt →
  ⊥
hepR43AcceptedGeneralLawReceiptImpossibleHere ()

data HEPDataMassWindowGeneralW3PromotionReceipt : Set where

hepR43W3PromotionReceiptImpossibleHere :
  HEPDataMassWindowGeneralW3PromotionReceipt →
  ⊥
hepR43W3PromotionReceiptImpossibleHere ()

record HEPDataMassWindowGeneralPredictionLawDiagnostic : Setω where
  field
    status :
      HEPDataMassWindowGeneralPredictionLawStatus

    upstreamPosteriorShapeResponseDiagnostic :
      R41.HEPDataT43PosteriorShapeResponseDiagnostic

    upstreamHoldoutValidationDiagnostic :
      R42.HEPDataT45HoldoutValidationDiagnostic

    hepR41T43Chi2PerDofString :
      String

    hepR41T43Chi2PerDofIsCanonical :
      hepR41T43Chi2PerDofString
      ≡
      "1.7408778006026118"

    hepR41T43NumericPass :
      Bool

    hepR41T43NumericPassIsTrue :
      hepR41T43NumericPass ≡ true

    hepR41Promoted :
      Bool

    hepR41PromotedIsFalse :
      hepR41Promoted ≡ false

    hepR41NoPromotionReason :
      String

    hepR41NoPromotionReasonIsCanonical :
      hepR41NoPromotionReason
      ≡
      "posterior response was tuned after t43 residual inspection"

    hepR42T45Chi2PerDofString :
      String

    hepR42T45Chi2PerDofIsCanonical :
      hepR42T45Chi2PerDofString
      ≡
      "222.54402462995546"

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

    hepR42ResidualRangeString :
      String

    hepR42ResidualRangeStringIsCanonical :
      hepR42ResidualRangeString
      ≡
      "-0.016478603959446673 to -0.014765036132624995"

    t45HoldoutFailureProves :
      String

    t45HoldoutFailureProvesIsCanonical :
      t45HoldoutFailureProves
      ≡
      "the t43 posterior numeric pass is not a mass-window-general empirical adequacy receipt"

    t44RoleCorrection :
      String

    t44RoleCorrectionIsCanonical :
      t44RoleCorrection
      ≡
      "t44 is the covariance companion for t43, not an independent validation ratio"

    requiredLowMassOverZPeakRatio :
      String

    requiredLowMassOverZPeakRatioIsCanonical :
      requiredLowMassOverZPeakRatio
      ≡
      "50-76/76-106"

    requiredHighMassOverZPeakRatio :
      String

    requiredHighMassOverZPeakRatioIsCanonical :
      requiredHighMassOverZPeakRatio
      ≡
      "106-170/76-106"

    observedTableTuningAllowed :
      Bool

    observedTableTuningAllowedIsFalse :
      observedTableTuningAllowed ≡ false

    governanceMarkers :
      List HEPDataMassWindowGeneralPredictionLawGovernanceMarker

    governanceMarkersAreCanonical :
      governanceMarkers
      ≡
      canonicalHEPDataMassWindowGeneralPredictionLawGovernanceMarkers

    nonPromotingMarker :
      HEPDataMassWindowGeneralPredictionLawGovernanceMarker

    nonPromotingMarkerIsCanonical :
      nonPromotingMarker ≡ NonPromoting

    w3BlockedMarker :
      HEPDataMassWindowGeneralPredictionLawGovernanceMarker

    w3BlockedMarkerIsCanonical :
      w3BlockedMarker ≡ W3Blocked

    cleanFreezeRequiredMarker :
      HEPDataMassWindowGeneralPredictionLawGovernanceMarker

    cleanFreezeRequiredMarkerIsCanonical :
      cleanFreezeRequiredMarker ≡ CleanFreezeRequired

    additionalHoldoutRequiredMarker :
      HEPDataMassWindowGeneralPredictionLawGovernanceMarker

    additionalHoldoutRequiredMarkerIsCanonical :
      additionalHoldoutRequiredMarker ≡ AdditionalHoldoutRequired

    diagnosticFields :
      List HEPDataMassWindowGeneralPredictionLawField

    diagnosticFieldsAreCanonical :
      diagnosticFields
      ≡
      canonicalHEPDataMassWindowGeneralPredictionLawFields

    boundaries :
      List HEPDataMassWindowGeneralPredictionLawBoundary

    boundariesAreCanonical :
      boundaries
      ≡
      canonicalHEPDataMassWindowGeneralPredictionLawBoundaries

    futureAcceptedGeneralLawReceiptBlocked :
      HEPDataMassWindowGeneralLawReceipt →
      ⊥

    futureW3PromotionBlocked :
      HEPDataMassWindowGeneralW3PromotionReceipt →
      ⊥

canonicalHEPDataMassWindowGeneralPredictionLawDiagnostic :
  HEPDataMassWindowGeneralPredictionLawDiagnostic
canonicalHEPDataMassWindowGeneralPredictionLawDiagnostic =
  record
    { status =
        massWindowGeneralLawRequiredAfterT45HoldoutFailure
    ; upstreamPosteriorShapeResponseDiagnostic =
        R41.canonicalHEPDataT43PosteriorShapeResponseDiagnostic
    ; upstreamHoldoutValidationDiagnostic =
        R42.canonicalHEPDataT45HoldoutValidationDiagnostic
    ; hepR41T43Chi2PerDofString =
        "1.7408778006026118"
    ; hepR41T43Chi2PerDofIsCanonical =
        refl
    ; hepR41T43NumericPass =
        true
    ; hepR41T43NumericPassIsTrue =
        refl
    ; hepR41Promoted =
        false
    ; hepR41PromotedIsFalse =
        refl
    ; hepR41NoPromotionReason =
        "posterior response was tuned after t43 residual inspection"
    ; hepR41NoPromotionReasonIsCanonical =
        refl
    ; hepR42T45Chi2PerDofString =
        "222.54402462995546"
    ; hepR42T45Chi2PerDofIsCanonical =
        refl
    ; hepR42DirtyProjectionFileSHA256 =
        "60242829cd37a9508c1b21da969c43383c1e00f6e4b6c77457ee5d1a67e2b4e3"
    ; hepR42DirtyProjectionFileSHA256IsCanonical =
        refl
    ; hepR42DirtyProjectionDigest =
        "2ac58b6d7c16384769dae42be2877c0025797acacc730f9d9443b00e538bda25"
    ; hepR42DirtyProjectionDigestIsCanonical =
        refl
    ; hepR42ResidualRangeString =
        "-0.016478603959446673 to -0.014765036132624995"
    ; hepR42ResidualRangeStringIsCanonical =
        refl
    ; t45HoldoutFailureProves =
        "the t43 posterior numeric pass is not a mass-window-general empirical adequacy receipt"
    ; t45HoldoutFailureProvesIsCanonical =
        refl
    ; t44RoleCorrection =
        "t44 is the covariance companion for t43, not an independent validation ratio"
    ; t44RoleCorrectionIsCanonical =
        refl
    ; requiredLowMassOverZPeakRatio =
        "50-76/76-106"
    ; requiredLowMassOverZPeakRatioIsCanonical =
        refl
    ; requiredHighMassOverZPeakRatio =
        "106-170/76-106"
    ; requiredHighMassOverZPeakRatioIsCanonical =
        refl
    ; observedTableTuningAllowed =
        false
    ; observedTableTuningAllowedIsFalse =
        refl
    ; governanceMarkers =
        canonicalHEPDataMassWindowGeneralPredictionLawGovernanceMarkers
    ; governanceMarkersAreCanonical =
        refl
    ; nonPromotingMarker =
        NonPromoting
    ; nonPromotingMarkerIsCanonical =
        refl
    ; w3BlockedMarker =
        W3Blocked
    ; w3BlockedMarkerIsCanonical =
        refl
    ; cleanFreezeRequiredMarker =
        CleanFreezeRequired
    ; cleanFreezeRequiredMarkerIsCanonical =
        refl
    ; additionalHoldoutRequiredMarker =
        AdditionalHoldoutRequired
    ; additionalHoldoutRequiredMarkerIsCanonical =
        refl
    ; diagnosticFields =
        canonicalHEPDataMassWindowGeneralPredictionLawFields
    ; diagnosticFieldsAreCanonical =
        refl
    ; boundaries =
        canonicalHEPDataMassWindowGeneralPredictionLawBoundaries
    ; boundariesAreCanonical =
        refl
    ; futureAcceptedGeneralLawReceiptBlocked =
        hepR43AcceptedGeneralLawReceiptImpossibleHere
    ; futureW3PromotionBlocked =
        hepR43W3PromotionReceiptImpossibleHere
    }

canonicalHEPDataMassWindowGeneralPredictionLawStatus :
  HEPDataMassWindowGeneralPredictionLawStatus
canonicalHEPDataMassWindowGeneralPredictionLawStatus =
  HEPDataMassWindowGeneralPredictionLawDiagnostic.status
    canonicalHEPDataMassWindowGeneralPredictionLawDiagnostic
