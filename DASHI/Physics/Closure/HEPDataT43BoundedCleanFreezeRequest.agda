module DASHI.Physics.Closure.HEPDataT43BoundedCleanFreezeRequest where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Float using (Float)
open import Agda.Builtin.String using (String)
open import Agda.Builtin.Unit using (⊤; tt)
open import Agda.Builtin.Equality using (_≡_; refl)

open import DASHI.Physics.Closure.HEPDataMassKernelCalibrationDiagnostic

------------------------------------------------------------------------
-- HEP-R50: bounded t43 clean-freeze request.
--
-- HEP-R49 established that the t45 blocker is upstream of the phi-star shape
-- wrapper: the above-Z neutral-current/PDF mass-kernel decomposition remains
-- unresolved and is recorded as pdfRequired.  This surface therefore narrows
-- the next clean run to the solved below-Z t43 lane only.
--
-- This is not a W3 promotion receipt.  It is the exact request surface for a
-- future clean projection run after the current diagnostic code and inputs
-- have been committed and the worktree has been verified clean.

data HEPDataT43CleanFreezeScope : Set where
  t43BelowZOnly :
    HEPDataT43CleanFreezeScope

data HEPDataT45Disposition : Set where
  parkedAsPDFRequired :
    HEPDataT45Disposition

data HEPDataT43CleanFreezeNextAction : Set where
  commitDiagnosticsThenFreeze :
    HEPDataT43CleanFreezeNextAction
  runT43ProjectionOnly :
    HEPDataT43CleanFreezeNextAction
  compareCleanT43Chi2 :
    HEPDataT43CleanFreezeNextAction

record HEPDataT43BoundedCleanFreezeRequest : Set where
  field
    scope :
      HEPDataT43CleanFreezeScope

    t43Table :
      String

    t43CovarianceTable :
      String

    predictionAPI :
      String

    diagnosticChi2PerDof :
      Float

    diagnosticMeanPredData :
      Float

    cleanChi2Threshold :
      Float

    requiresCleanWorktree :
      Bool

    requiresPredictionFixedAt :
      Bool

    requiresProjectionDigest :
      Bool

    t45Disposition :
      HEPDataT45Disposition

    t45BlockingReceipt :
      HEPDataMassKernelCalibrationDiagnostic

    t45StatusIsPDFRequired :
      HEPDataMassKernelCalibrationDiagnostic.massKernelStatus t45BlockingReceipt
        ≡ pdfRequired

    nextAction :
      HEPDataT43CleanFreezeNextAction

    -- Guardrail: this request does not itself promote W3.  Promotion needs a
    -- clean predictionFixedAt, a committed projection artifact, and a clean
    -- t43 comparison-law receipt.
    noPromotionHere :
      ⊤

canonicalHEPDataT43BoundedCleanFreezeRequest :
  HEPDataT43BoundedCleanFreezeRequest
canonicalHEPDataT43BoundedCleanFreezeRequest =
  record
    { scope = t43BelowZOnly
    ; t43Table = "ins2079374/t43"
    ; t43CovarianceTable = "ins2079374/t44"
    ; predictionAPI = "DASHI.Physics.Prediction.sigma_dashi:predict_ratio"
    ; diagnosticChi2PerDof = 2.1565191176
    ; diagnosticMeanPredData = 0.9941233097
    ; cleanChi2Threshold = 4.0
    ; requiresCleanWorktree = true
    ; requiresPredictionFixedAt = true
    ; requiresProjectionDigest = true
    ; t45Disposition = parkedAsPDFRequired
    ; t45BlockingReceipt = canonicalHEPDataMassKernelCalibrationDiagnostic
    ; t45StatusIsPDFRequired = refl
    ; nextAction = commitDiagnosticsThenFreeze
    ; noPromotionHere = tt
    }

canonicalHEPDataT43BoundedCleanFreezeNoPromotion :
  HEPDataT43BoundedCleanFreezeRequest.noPromotionHere
    canonicalHEPDataT43BoundedCleanFreezeRequest
    ≡ tt
canonicalHEPDataT43BoundedCleanFreezeNoPromotion = refl
