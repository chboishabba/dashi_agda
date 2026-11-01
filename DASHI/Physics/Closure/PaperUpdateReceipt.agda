module DASHI.Physics.Closure.PaperUpdateReceipt where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

------------------------------------------------------------------------
-- Manager C task C5: paper update receipt.
--
-- This receipt records prose-update state only.  It names the Paper 6 CP
-- phase diagnostic section update, the Paper 8 Shimura tower spatial
-- refinement update, and the internal-review gate required before submission.
-- It deliberately promotes no claim.

data PaperUpdateItem : Set where
  paper6CPPhaseDiagnosticSectionUpdate :
    PaperUpdateItem

  paper8ShimuraTowerSpatialRefinementUpdate :
    PaperUpdateItem

  internalReviewRequiredBeforeSubmission :
    PaperUpdateItem

canonicalPaperUpdateItems :
  List PaperUpdateItem
canonicalPaperUpdateItems =
  paper6CPPhaseDiagnosticSectionUpdate
  ∷ paper8ShimuraTowerSpatialRefinementUpdate
  ∷ internalReviewRequiredBeforeSubmission
  ∷ []

paper6CPPhaseDiagnosticSectionUpdateText : String
paper6CPPhaseDiagnosticSectionUpdateText =
  "Paper 6 update: CP phase diagnostic section is recorded as an internal diagnostic section update, not as a physical CKM or CP-violation promotion."

paper8ShimuraTowerSpatialRefinementUpdateText : String
paper8ShimuraTowerSpatialRefinementUpdateText =
  "Paper 8 update: Shimura tower spatial refinement is recorded as a draft refinement update, not as a terminal unification or exact Standard Model promotion."

internalReviewRequiredBeforeSubmissionText : String
internalReviewRequiredBeforeSubmissionText =
  "Internal review is required before submission for the updated paper sections."

paperUpdateReceiptStatement : String
paperUpdateReceiptStatement =
  "C5 paper update receipt records Paper 6 CP phase diagnostic section update, Paper 8 Shimura tower spatial refinement update, and internal review required before submission; no claims are promoted."

data PaperUpdatePromotion : Set where

paperUpdatePromotionImpossibleHere :
  PaperUpdatePromotion →
  ⊥
paperUpdatePromotionImpossibleHere ()

record PaperUpdateReceipt : Setω where
  field
    updateItems :
      List PaperUpdateItem

    updateItemsAreCanonical :
      updateItems ≡ canonicalPaperUpdateItems

    paper6CPPhaseDiagnosticSectionUpdated :
      Bool

    paper6CPPhaseDiagnosticSectionUpdatedIsTrue :
      paper6CPPhaseDiagnosticSectionUpdated ≡ true

    paper6CPPhaseDiagnosticSectionUpdateRecordedAs :
      String

    paper6CPPhaseDiagnosticSectionUpdateRecordedAsCanonical :
      paper6CPPhaseDiagnosticSectionUpdateRecordedAs
        ≡ paper6CPPhaseDiagnosticSectionUpdateText

    paper8ShimuraTowerSpatialRefinementUpdated :
      Bool

    paper8ShimuraTowerSpatialRefinementUpdatedIsTrue :
      paper8ShimuraTowerSpatialRefinementUpdated ≡ true

    paper8ShimuraTowerSpatialRefinementUpdateRecordedAs :
      String

    paper8ShimuraTowerSpatialRefinementUpdateRecordedAsCanonical :
      paper8ShimuraTowerSpatialRefinementUpdateRecordedAs
        ≡ paper8ShimuraTowerSpatialRefinementUpdateText

    internalReviewRequiredBeforeSubmissionFlag :
      Bool

    internalReviewRequiredBeforeSubmissionFlagIsTrue :
      internalReviewRequiredBeforeSubmissionFlag ≡ true

    internalReviewGateRecordedAs :
      String

    internalReviewGateRecordedAsCanonical :
      internalReviewGateRecordedAs
        ≡ internalReviewRequiredBeforeSubmissionText

    submissionReadyWithoutInternalReview :
      Bool

    submissionReadyWithoutInternalReviewIsFalse :
      submissionReadyWithoutInternalReview ≡ false

    governanceOnly :
      Bool

    governanceOnlyIsTrue :
      governanceOnly ≡ true

    paper6ClaimPromoted :
      Bool

    paper6ClaimPromotedIsFalse :
      paper6ClaimPromoted ≡ false

    paper8ClaimPromoted :
      Bool

    paper8ClaimPromotedIsFalse :
      paper8ClaimPromoted ≡ false

    cpPhaseClaimPromoted :
      Bool

    cpPhaseClaimPromotedIsFalse :
      cpPhaseClaimPromoted ≡ false

    shimuraTowerClaimPromoted :
      Bool

    shimuraTowerClaimPromotedIsFalse :
      shimuraTowerClaimPromoted ≡ false

    submissionClaimPromoted :
      Bool

    submissionClaimPromotedIsFalse :
      submissionClaimPromoted ≡ false

    terminalClaimPromoted :
      Bool

    terminalClaimPromotedIsFalse :
      terminalClaimPromoted ≡ false

    promotionFlags :
      List PaperUpdatePromotion

    promotionFlagsAreEmpty :
      promotionFlags ≡ []

    statement :
      String

    statementIsCanonical :
      statement ≡ paperUpdateReceiptStatement

    receiptBoundary :
      List String

open PaperUpdateReceipt public

canonicalPaperUpdateReceipt :
  PaperUpdateReceipt
canonicalPaperUpdateReceipt =
  record
    { updateItems =
        canonicalPaperUpdateItems
    ; updateItemsAreCanonical =
        refl
    ; paper6CPPhaseDiagnosticSectionUpdated =
        true
    ; paper6CPPhaseDiagnosticSectionUpdatedIsTrue =
        refl
    ; paper6CPPhaseDiagnosticSectionUpdateRecordedAs =
        paper6CPPhaseDiagnosticSectionUpdateText
    ; paper6CPPhaseDiagnosticSectionUpdateRecordedAsCanonical =
        refl
    ; paper8ShimuraTowerSpatialRefinementUpdated =
        true
    ; paper8ShimuraTowerSpatialRefinementUpdatedIsTrue =
        refl
    ; paper8ShimuraTowerSpatialRefinementUpdateRecordedAs =
        paper8ShimuraTowerSpatialRefinementUpdateText
    ; paper8ShimuraTowerSpatialRefinementUpdateRecordedAsCanonical =
        refl
    ; internalReviewRequiredBeforeSubmissionFlag =
        true
    ; internalReviewRequiredBeforeSubmissionFlagIsTrue =
        refl
    ; internalReviewGateRecordedAs =
        internalReviewRequiredBeforeSubmissionText
    ; internalReviewGateRecordedAsCanonical =
        refl
    ; submissionReadyWithoutInternalReview =
        false
    ; submissionReadyWithoutInternalReviewIsFalse =
        refl
    ; governanceOnly =
        true
    ; governanceOnlyIsTrue =
        refl
    ; paper6ClaimPromoted =
        false
    ; paper6ClaimPromotedIsFalse =
        refl
    ; paper8ClaimPromoted =
        false
    ; paper8ClaimPromotedIsFalse =
        refl
    ; cpPhaseClaimPromoted =
        false
    ; cpPhaseClaimPromotedIsFalse =
        refl
    ; shimuraTowerClaimPromoted =
        false
    ; shimuraTowerClaimPromotedIsFalse =
        refl
    ; submissionClaimPromoted =
        false
    ; submissionClaimPromotedIsFalse =
        refl
    ; terminalClaimPromoted =
        false
    ; terminalClaimPromotedIsFalse =
        refl
    ; promotionFlags =
        []
    ; promotionFlagsAreEmpty =
        refl
    ; statement =
        paperUpdateReceiptStatement
    ; statementIsCanonical =
        refl
    ; receiptBoundary =
        "Manager C task C5 records paper-update status only"
        ∷ "Paper 6 CP phase diagnostic section update is recorded"
        ∷ "Paper 8 Shimura tower spatial refinement update is recorded"
        ∷ "Internal review is required before submission"
        ∷ "Submission-ready-without-internal-review remains false"
        ∷ "No Paper 6, Paper 8, CP phase, Shimura tower, submission, or terminal claim is promoted"
        ∷ []
    }

paperUpdateRequiresInternalReview :
  internalReviewRequiredBeforeSubmissionFlag canonicalPaperUpdateReceipt ≡ true
paperUpdateRequiresInternalReview =
  refl

paperUpdateNotSubmissionReadyWithoutReview :
  submissionReadyWithoutInternalReview canonicalPaperUpdateReceipt ≡ false
paperUpdateNotSubmissionReadyWithoutReview =
  refl

paperUpdateKeepsPaper6ClaimFalse :
  paper6ClaimPromoted canonicalPaperUpdateReceipt ≡ false
paperUpdateKeepsPaper6ClaimFalse =
  refl

paperUpdateKeepsPaper8ClaimFalse :
  paper8ClaimPromoted canonicalPaperUpdateReceipt ≡ false
paperUpdateKeepsPaper8ClaimFalse =
  refl

paperUpdateKeepsTerminalFalse :
  terminalClaimPromoted canonicalPaperUpdateReceipt ≡ false
paperUpdateKeepsTerminalFalse =
  refl

paperUpdateNoPromotion :
  PaperUpdatePromotion →
  ⊥
paperUpdateNoPromotion =
  paperUpdatePromotionImpossibleHere
