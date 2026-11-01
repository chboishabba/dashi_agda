module DASHI.Physics.Closure.SessionTagFinalReceipt where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

------------------------------------------------------------------------
-- Manager C final session tag receipt for phase2-frontier-v1.

sessionTagToLand : String
sessionTagToLand =
  "phase2-frontier-v1"

phase2FrontierCommitMessageSummary : String
phase2FrontierCommitMessageSummary =
  "Land phase2-frontier-v1: complete frontier state recorded; NS and YM each retain one Clay gap; Yukawa/CKM retains beta-from-carrier gap; Papers 6 and 8 are draft-complete and ready for internal review; all Clay and terminal promotions remain false."

data FrontierRecordedState : Set where
  completeFrontierStateRecorded :
    FrontierRecordedState

data ClayProblem : Set where
  navierStokesClay :
    ClayProblem

  yangMillsClay :
    ClayProblem

canonicalClayProblems : List ClayProblem
canonicalClayProblems =
  navierStokesClay
  ∷ yangMillsClay
  ∷ []

data ClayGap : Set where
  oneNavierStokesGap :
    ClayGap

  oneYangMillsGap :
    ClayGap

canonicalClayGaps : List ClayGap
canonicalClayGaps =
  oneNavierStokesGap
  ∷ oneYangMillsGap
  ∷ []

data YukawaCKMGap : Set where
  betaFromCarrierGap :
    YukawaCKMGap

data PaperDraft : Set where
  paper6DraftComplete :
    PaperDraft

  paper8DraftComplete :
    PaperDraft

canonicalDraftCompletePapers : List PaperDraft
canonicalDraftCompletePapers =
  paper6DraftComplete
  ∷ paper8DraftComplete
  ∷ []

data ReviewReadiness : Set where
  readyForInternalReview :
    ReviewReadiness

data SessionTagPromotion : Set where

sessionTagPromotionImpossibleHere :
  SessionTagPromotion →
  ⊥
sessionTagPromotionImpossibleHere ()

sessionTagFinalStatement : String
sessionTagFinalStatement =
  "Manager C final tag receipt: phase2-frontier-v1 is ready to land as a state receipt; the full frontier is recorded; NS and YM each retain one Clay gap; Yukawa/CKM retains the beta-from-carrier gap; Papers 6 and 8 are draft-complete and ready for internal review; no Clay or terminal promotion is made."

record SessionTagFinalReceipt : Setω where
  field
    tagToLand :
      String

    tagToLandIsCanonical :
      tagToLand ≡ sessionTagToLand

    commitMessageSummary :
      String

    commitMessageSummaryIsCanonical :
      commitMessageSummary ≡ phase2FrontierCommitMessageSummary

    frontierState :
      FrontierRecordedState

    frontierStateIsComplete :
      frontierState ≡ completeFrontierStateRecorded

    completeFrontierStateRecordedFlag :
      Bool

    completeFrontierStateRecordedFlagIsTrue :
      completeFrontierStateRecordedFlag ≡ true

    clayProblems :
      List ClayProblem

    clayProblemsAreCanonical :
      clayProblems ≡ canonicalClayProblems

    clayGaps :
      List ClayGap

    clayGapsAreCanonical :
      clayGaps ≡ canonicalClayGaps

    navierStokesGap :
      ClayGap

    navierStokesGapIsOneGap :
      navierStokesGap ≡ oneNavierStokesGap

    yangMillsGap :
      ClayGap

    yangMillsGapIsOneGap :
      yangMillsGap ≡ oneYangMillsGap

    yukawaCKMGap :
      YukawaCKMGap

    yukawaCKMGapIsBetaFromCarrier :
      yukawaCKMGap ≡ betaFromCarrierGap

    draftCompletePapers :
      List PaperDraft

    draftCompletePapersAreCanonical :
      draftCompletePapers ≡ canonicalDraftCompletePapers

    paper6ReviewReadiness :
      ReviewReadiness

    paper6ReadyForInternalReview :
      paper6ReviewReadiness ≡ readyForInternalReview

    paper8ReviewReadiness :
      ReviewReadiness

    paper8ReadyForInternalReview :
      paper8ReviewReadiness ≡ readyForInternalReview

    paper6DraftCompleteRecorded :
      Bool

    paper6DraftCompleteRecordedIsTrue :
      paper6DraftCompleteRecorded ≡ true

    paper8DraftCompleteRecorded :
      Bool

    paper8DraftCompleteRecordedIsTrue :
      paper8DraftCompleteRecorded ≡ true

    clayNavierStokesPromoted :
      Bool

    clayNavierStokesPromotedIsFalse :
      clayNavierStokesPromoted ≡ false

    clayYangMillsPromoted :
      Bool

    clayYangMillsPromotedIsFalse :
      clayYangMillsPromoted ≡ false

    terminalClayClaimPromoted :
      Bool

    terminalClayClaimPromotedIsFalse :
      terminalClayClaimPromoted ≡ false

    terminalPhysicsClaimPromoted :
      Bool

    terminalPhysicsClaimPromotedIsFalse :
      terminalPhysicsClaimPromoted ≡ false

    terminalPaperClaimPromoted :
      Bool

    terminalPaperClaimPromotedIsFalse :
      terminalPaperClaimPromoted ≡ false

    promotionFlags :
      List SessionTagPromotion

    promotionFlagsAreEmpty :
      promotionFlags ≡ []

    statement :
      String

    statementIsCanonical :
      statement ≡ sessionTagFinalStatement

    receiptBoundary :
      List String

open SessionTagFinalReceipt public

canonicalSessionTagFinalReceipt :
  SessionTagFinalReceipt
canonicalSessionTagFinalReceipt =
  record
    { tagToLand =
        sessionTagToLand
    ; tagToLandIsCanonical =
        refl
    ; commitMessageSummary =
        phase2FrontierCommitMessageSummary
    ; commitMessageSummaryIsCanonical =
        refl
    ; frontierState =
        completeFrontierStateRecorded
    ; frontierStateIsComplete =
        refl
    ; completeFrontierStateRecordedFlag =
        true
    ; completeFrontierStateRecordedFlagIsTrue =
        refl
    ; clayProblems =
        canonicalClayProblems
    ; clayProblemsAreCanonical =
        refl
    ; clayGaps =
        canonicalClayGaps
    ; clayGapsAreCanonical =
        refl
    ; navierStokesGap =
        oneNavierStokesGap
    ; navierStokesGapIsOneGap =
        refl
    ; yangMillsGap =
        oneYangMillsGap
    ; yangMillsGapIsOneGap =
        refl
    ; yukawaCKMGap =
        betaFromCarrierGap
    ; yukawaCKMGapIsBetaFromCarrier =
        refl
    ; draftCompletePapers =
        canonicalDraftCompletePapers
    ; draftCompletePapersAreCanonical =
        refl
    ; paper6ReviewReadiness =
        readyForInternalReview
    ; paper6ReadyForInternalReview =
        refl
    ; paper8ReviewReadiness =
        readyForInternalReview
    ; paper8ReadyForInternalReview =
        refl
    ; paper6DraftCompleteRecorded =
        true
    ; paper6DraftCompleteRecordedIsTrue =
        refl
    ; paper8DraftCompleteRecorded =
        true
    ; paper8DraftCompleteRecordedIsTrue =
        refl
    ; clayNavierStokesPromoted =
        false
    ; clayNavierStokesPromotedIsFalse =
        refl
    ; clayYangMillsPromoted =
        false
    ; clayYangMillsPromotedIsFalse =
        refl
    ; terminalClayClaimPromoted =
        false
    ; terminalClayClaimPromotedIsFalse =
        refl
    ; terminalPhysicsClaimPromoted =
        false
    ; terminalPhysicsClaimPromotedIsFalse =
        refl
    ; terminalPaperClaimPromoted =
        false
    ; terminalPaperClaimPromotedIsFalse =
        refl
    ; promotionFlags =
        []
    ; promotionFlagsAreEmpty =
        refl
    ; statement =
        sessionTagFinalStatement
    ; statementIsCanonical =
        refl
    ; receiptBoundary =
        "Tag to land is phase2-frontier-v1"
        ∷ "Complete frontier state is recorded"
        ∷ "Navier-Stokes and Yang-Mills each retain exactly one Clay gap in this receipt"
        ∷ "Yukawa/CKM retains the beta-from-carrier gap"
        ∷ "Papers 6 and 8 are draft-complete and ready for internal review"
        ∷ "All Clay and terminal promotion flags remain false"
        ∷ []
    }

sessionTagFinalTagCanonical :
  tagToLand canonicalSessionTagFinalReceipt ≡ sessionTagToLand
sessionTagFinalTagCanonical =
  refl

sessionTagFinalFrontierComplete :
  completeFrontierStateRecordedFlag canonicalSessionTagFinalReceipt ≡ true
sessionTagFinalFrontierComplete =
  refl

sessionTagFinalKeepsNSClayFalse :
  clayNavierStokesPromoted canonicalSessionTagFinalReceipt ≡ false
sessionTagFinalKeepsNSClayFalse =
  refl

sessionTagFinalKeepsYMClayFalse :
  clayYangMillsPromoted canonicalSessionTagFinalReceipt ≡ false
sessionTagFinalKeepsYMClayFalse =
  refl

sessionTagFinalKeepsTerminalClayFalse :
  terminalClayClaimPromoted canonicalSessionTagFinalReceipt ≡ false
sessionTagFinalKeepsTerminalClayFalse =
  refl

sessionTagFinalKeepsTerminalPhysicsFalse :
  terminalPhysicsClaimPromoted canonicalSessionTagFinalReceipt ≡ false
sessionTagFinalKeepsTerminalPhysicsFalse =
  refl

sessionTagFinalKeepsTerminalPaperFalse :
  terminalPaperClaimPromoted canonicalSessionTagFinalReceipt ≡ false
sessionTagFinalKeepsTerminalPaperFalse =
  refl

sessionTagFinalNoPromotion :
  SessionTagPromotion →
  ⊥
sessionTagFinalNoPromotion =
  sessionTagPromotionImpossibleHere
