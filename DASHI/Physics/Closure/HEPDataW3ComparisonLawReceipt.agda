module DASHI.Physics.Closure.HEPDataW3ComparisonLawReceipt where

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Float using (Float)
open import Agda.Builtin.String using (String)
open import Agda.Builtin.Unit using (⊤; tt)

open import DASHI.Physics.Closure.HEPDataMassKernelCalibrationDiagnostic
open import DASHI.Physics.Closure.HEPDataT43BoundedCleanFreezeRequest
open import DASHI.Physics.Closure.HEPDataW3PromotionCandidate

------------------------------------------------------------------------
-- HEP-R52: W3 comparison-law receipt for the bounded t43 lane.
--
-- HEP-R51 recorded a clean, deterministic promotion candidate, but kept the
-- runner boundary honest: comparisonLawStatus = "not-claimed".  This receipt
-- consumes the covariance-aware chi2 recomputation against the t44 covariance
-- companion and records the W3 comparison-law decision.
--
-- Scope is intentionally narrow: t43 below-Z only.  The above-Z t45/t46 lane
-- remains parked as pdfRequired by HEPDataMassKernelCalibrationDiagnostic and
-- is routed to the W5/PDF obligation, not silently promoted through W3.

data HEPDataW3ComparisonLawReceiptStatus : Set where
  claimedByCovarianceReview :
    HEPDataW3ComparisonLawReceiptStatus

data W3ComparisonLawScope : Set where
  t43BelowZMassWindowRatio :
    W3ComparisonLawScope

data W3ObservableConvention : Set where
  unnormalizedDifferentialCrossSectionRatio :
    W3ObservableConvention

data W3PromotionStatus : Set where
  promotedT43BelowZOnly :
    W3PromotionStatus

data W3DownstreamGateStatus : Set where
  unblockedByT43ComparisonLaw :
    W3DownstreamGateStatus
  blockedPDFRequired :
    W3DownstreamGateStatus

record W3ComparisonLawAcceptanceCriterion : Set where
  field
    candidate :
      HEPDataW3PromotionCandidate

    chi2 :
      Float

    chi2PerDof :
      Float

    nBins :
      Float

    effectiveDof :
      Float

    acceptanceThreshold :
      Float

    meanPredData :
      Float

    meanPredDataLowerBound :
      Float

    meanPredDataUpperBound :
      Float

    covarianceSource :
      String

    freezeCommit :
      String

    fileSha256 :
      String

    projectionDigest :
      String

    t43DigestStatus :
      Bool

    t44DigestStatus :
      Bool

    t43CovarianceUsed :
      Bool

    -- Numeric comparison has been performed outside Agda over the clean
    -- projection artifact: chi2/dof = 2.1565191176 < 4.0 and mean pred/data
    -- = 0.9941233097 lies in [0.97, 1.03].
    criterionSatisfied :
      Bool

    candidateNumericPass :
      HEPDataW3PromotionCandidate.cleanRunNumericPass candidate ≡ true

record W3ComparisonLawScopeBoundary : Set where
  field
    scope :
      W3ComparisonLawScope

    observableConvention :
      W3ObservableConvention

    t43Table :
      String

    t44CovarianceTable :
      String

    t45Disposition :
      HEPDataT45Disposition

    t45BlockingReceipt :
      HEPDataMassKernelCalibrationDiagnostic

    t45StatusIsPDFRequired :
      HEPDataMassKernelCalibrationDiagnostic.massKernelStatus t45BlockingReceipt
        ≡ pdfRequired

    aboveZStatus :
      W3DownstreamGateStatus

    noAboveZPromotionHere :
      ⊤

record W3ComparisonLawReceipt : Set where
  field
    candidate :
      HEPDataW3PromotionCandidate

    criterion :
      W3ComparisonLawAcceptanceCriterion

    scopeBoundary :
      W3ComparisonLawScopeBoundary

    comparisonLawStatus :
      HEPDataW3ComparisonLawReceiptStatus

    w3Status :
      W3PromotionStatus

    w4Gate :
      W3DownstreamGateStatus

    w8Gate :
      W3DownstreamGateStatus

    w5Gate :
      W3DownstreamGateStatus

    -- W3 promotion is bounded to the below-Z t43 comparison-law lane.  This
    -- is not a W4 calibration receipt, a W5 PDF/GRQFT receipt, a W6 runtime
    -- receipt, or a W8 external authority token.
    boundedPromotionOnly :
      ⊤

canonicalW3ComparisonLawAcceptanceCriterion :
  W3ComparisonLawAcceptanceCriterion
canonicalW3ComparisonLawAcceptanceCriterion =
  record
    { candidate = canonicalHEPDataW3PromotionCandidate
    ; chi2 = 38.8173441173
    ; chi2PerDof = 2.1565191176
    ; nBins = 18.0
    ; effectiveDof = 18.0
    ; acceptanceThreshold = 4.0
    ; meanPredData = 0.9941233097
    ; meanPredDataLowerBound = 0.97
    ; meanPredDataUpperBound = 1.03
    ; covarianceSource = "ins2079374/t44"
    ; freezeCommit =
        "3205d746639568762c9e97adf4a3672c356bd491"
    ; fileSha256 =
        "ffd659e6e2f271d75ec6bf90c5be34cbb9959a8f9d32762c1a2231835fb61eac"
    ; projectionDigest =
        "00f6c23f97f9c0275d90e6ffbf6151b07defcc163708e2d93982d9b7d6866035"
    ; t43DigestStatus = true
    ; t44DigestStatus = true
    ; t43CovarianceUsed = true
    ; criterionSatisfied = true
    ; candidateNumericPass = refl
    }

canonicalW3ComparisonLawScopeBoundary :
  W3ComparisonLawScopeBoundary
canonicalW3ComparisonLawScopeBoundary =
  record
    { scope = t43BelowZMassWindowRatio
    ; observableConvention = unnormalizedDifferentialCrossSectionRatio
    ; t43Table = "ins2079374/t43"
    ; t44CovarianceTable = "ins2079374/t44"
    ; t45Disposition = parkedAsPDFRequired
    ; t45BlockingReceipt = canonicalHEPDataMassKernelCalibrationDiagnostic
    ; t45StatusIsPDFRequired = refl
    ; aboveZStatus = blockedPDFRequired
    ; noAboveZPromotionHere = tt
    }

canonicalHEPDataW3ComparisonLawReceipt :
  W3ComparisonLawReceipt
canonicalHEPDataW3ComparisonLawReceipt =
  record
    { candidate = canonicalHEPDataW3PromotionCandidate
    ; criterion = canonicalW3ComparisonLawAcceptanceCriterion
    ; scopeBoundary = canonicalW3ComparisonLawScopeBoundary
    ; comparisonLawStatus = claimedByCovarianceReview
    ; w3Status = promotedT43BelowZOnly
    ; w4Gate = unblockedByT43ComparisonLaw
    ; w8Gate = unblockedByT43ComparisonLaw
    ; w5Gate = blockedPDFRequired
    ; boundedPromotionOnly = tt
    }

canonicalHEPDataW3ComparisonLawReceiptPromotesW3 :
  W3ComparisonLawReceipt.w3Status canonicalHEPDataW3ComparisonLawReceipt
    ≡ promotedT43BelowZOnly
canonicalHEPDataW3ComparisonLawReceiptPromotesW3 = refl

canonicalHEPDataW3ComparisonLawReceiptKeepsT45Parked :
  W3ComparisonLawScopeBoundary.t45StatusIsPDFRequired
    canonicalW3ComparisonLawScopeBoundary
    ≡ refl
canonicalHEPDataW3ComparisonLawReceiptKeepsT45Parked = refl
