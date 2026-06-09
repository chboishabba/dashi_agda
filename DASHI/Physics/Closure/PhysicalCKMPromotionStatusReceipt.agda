module DASHI.Physics.Closure.PhysicalCKMPromotionStatusReceipt where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Physics.Closure.CKMDiagnosticSummaryReceipt as Summary

------------------------------------------------------------------------
-- Physical CKM promotion status receipt.
--
-- Terminal promotion status for the current tranche: fail closed.

data PhysicalCKMPromotionStatus : Set where
  physicalCKMPromotionRejectedByCurrentDiagnostics :
    PhysicalCKMPromotionStatus

data PhysicalCKMPromotionBlocker : Set where
  fullMatrixDiagnosticNotPhysicalAuthority :
    PhysicalCKMPromotionBlocker

  vubNaiveCarrierRouteFailsPDG :
    PhysicalCKMPromotionBlocker

  anomalyCancellationStillConditional :
    PhysicalCKMPromotionBlocker

  yukawaEigenbasisAndNormalisationAuthorityMissing :
    PhysicalCKMPromotionBlocker

canonicalPhysicalCKMPromotionBlockers :
  List PhysicalCKMPromotionBlocker
canonicalPhysicalCKMPromotionBlockers =
  fullMatrixDiagnosticNotPhysicalAuthority
  ∷ vubNaiveCarrierRouteFailsPDG
  ∷ anomalyCancellationStillConditional
  ∷ yukawaEigenbasisAndNormalisationAuthorityMissing
  ∷ []

data PhysicalCKMPromotionToken : Set where

physicalCKMPromotionTokenImpossibleHere :
  PhysicalCKMPromotionToken →
  ⊥
physicalCKMPromotionTokenImpossibleHere ()

terminalCKMDecisionLabel : String
terminalCKMDecisionLabel =
  "final CKM promotion status: false"

record PhysicalCKMPromotionStatusReceipt : Setω where
  field
    status :
      PhysicalCKMPromotionStatus

    diagnosticSummaryReceipt :
      Summary.CKMDiagnosticSummaryReceipt

    diagnosticSummaryKeepsCKMFalse :
      Bool

    diagnosticSummaryKeepsCKMFalseIsTrue :
      diagnosticSummaryKeepsCKMFalse ≡ true

    terminalDecision :
      String

    terminalDecisionIsCanonical :
      terminalDecision ≡ terminalCKMDecisionLabel

    diagnosticsCompleteForThisTranche :
      Bool

    diagnosticsCompleteForThisTrancheIsTrue :
      diagnosticsCompleteForThisTranche ≡ true

    physicalCKMPromoted :
      Bool

    physicalCKMPromotedIsFalse :
      physicalCKMPromoted ≡ false

    terminalPromotionFlag :
      Bool

    terminalPromotionFlagIsFalse :
      terminalPromotionFlag ≡ false

    terminalPromotionAgreesWithSummary :
      terminalPromotionFlag
      ≡
      Summary.physicalCKMPromoted diagnosticSummaryReceipt

    blockers :
      List PhysicalCKMPromotionBlocker

    blockersAreCanonical :
      blockers ≡ canonicalPhysicalCKMPromotionBlockers

    promotionTokens :
      List PhysicalCKMPromotionToken

    promotionTokensAreEmpty :
      promotionTokens ≡ []

    receiptBoundary :
      List String

open PhysicalCKMPromotionStatusReceipt public

canonicalPhysicalCKMPromotionStatusReceipt :
  PhysicalCKMPromotionStatusReceipt
canonicalPhysicalCKMPromotionStatusReceipt =
  record
    { status =
        physicalCKMPromotionRejectedByCurrentDiagnostics
    ; diagnosticSummaryReceipt =
        Summary.canonicalCKMDiagnosticSummaryReceipt
    ; diagnosticSummaryKeepsCKMFalse =
        true
    ; diagnosticSummaryKeepsCKMFalseIsTrue =
        refl
    ; terminalDecision =
        terminalCKMDecisionLabel
    ; terminalDecisionIsCanonical =
        refl
    ; diagnosticsCompleteForThisTranche =
        true
    ; diagnosticsCompleteForThisTrancheIsTrue =
        refl
    ; physicalCKMPromoted =
        false
    ; physicalCKMPromotedIsFalse =
        refl
    ; terminalPromotionFlag =
        false
    ; terminalPromotionFlagIsFalse =
        refl
    ; terminalPromotionAgreesWithSummary =
        refl
    ; blockers =
        canonicalPhysicalCKMPromotionBlockers
    ; blockersAreCanonical =
        refl
    ; promotionTokens =
        []
    ; promotionTokensAreEmpty =
        refl
    ; receiptBoundary =
        "The CKM/anomaly tranche has been recorded as diagnostics and conditional inheritance"
        ∷ "The naive Vub route fails, the degree-12 route is inconsistent, and anomaly cancellation is conditional"
        ∷ "The terminal physical CKM promotion flag is false"
        ∷ []
    }

physicalCKMPromotionStatusIsFalse :
  physicalCKMPromoted canonicalPhysicalCKMPromotionStatusReceipt ≡ false
physicalCKMPromotionStatusIsFalse =
  refl
