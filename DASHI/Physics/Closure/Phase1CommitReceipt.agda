module DASHI.Physics.Closure.Phase1CommitReceipt where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Physics.Closure.CommitTagPreparationReceipt as Prep

------------------------------------------------------------------------
-- Definitive Phase 1 commit/tag message preparation.

phase1CommitTitle : String
phase1CommitTitle =
  "Phase 1 frontier complete: Heegner-CKM diagnostic v2"

phase1TagName : String
phase1TagName =
  "heegner-ckm-v2-diagnostic"

data CommitSection : Set where
  derivedResults :
    CommitSection

  diagnosticResults :
    CommitSection

  honestNegativeResults :
    CommitSection

  falseTerminalFlags :
    CommitSection

canonicalCommitSections : List CommitSection
canonicalCommitSections =
  derivedResults
  ∷ diagnosticResults
  ∷ honestNegativeResults
  ∷ falseTerminalFlags
  ∷ []

record Phase1CommitReceipt : Setω where
  field
    preparationReceipt :
      Prep.CommitTagPreparationReceipt

    previousTagStillNotCreatedHere :
      Prep.tagCreatedHere preparationReceipt ≡ false

    phase1CommitMessageDrafted :
      Bool

    phase1CommitMessageDraftedIsTrue :
      phase1CommitMessageDrafted ≡ true

    tagName :
      String

    tagNameIsCanonical :
      tagName ≡ phase1TagName

    title :
      String

    titleIsCanonical :
      title ≡ phase1CommitTitle

    sections :
      List CommitSection

    sectionsAreCanonical :
      sections ≡ canonicalCommitSections

    commitCreatedHere :
      Bool

    commitCreatedHereIsFalse :
      commitCreatedHere ≡ false

    tagCreatedHere :
      Bool

    tagCreatedHereIsFalse :
      tagCreatedHere ≡ false

    clayYangMillsPromoted :
      Bool

    clayYangMillsPromotedIsFalse :
      clayYangMillsPromoted ≡ false

    clayNavierStokesPromoted :
      Bool

    clayNavierStokesPromotedIsFalse :
      clayNavierStokesPromoted ≡ false

    terminalUnificationPromoted :
      Bool

    terminalUnificationPromotedIsFalse :
      terminalUnificationPromoted ≡ false

    receiptBoundary :
      List String

open Phase1CommitReceipt public

canonicalPhase1CommitReceipt : Phase1CommitReceipt
canonicalPhase1CommitReceipt =
  record
    { preparationReceipt =
        Prep.canonicalCommitTagPreparationReceipt
    ; previousTagStillNotCreatedHere =
        refl
    ; phase1CommitMessageDrafted =
        true
    ; phase1CommitMessageDraftedIsTrue =
        refl
    ; tagName =
        phase1TagName
    ; tagNameIsCanonical =
        refl
    ; title =
        phase1CommitTitle
    ; titleIsCanonical =
        refl
    ; sections =
        canonicalCommitSections
    ; sectionsAreCanonical =
        refl
    ; commitCreatedHere =
        false
    ; commitCreatedHereIsFalse =
        refl
    ; tagCreatedHere =
        false
    ; tagCreatedHereIsFalse =
        refl
    ; clayYangMillsPromoted =
        false
    ; clayYangMillsPromotedIsFalse =
        refl
    ; clayNavierStokesPromoted =
        false
    ; clayNavierStokesPromotedIsFalse =
        refl
    ; terminalUnificationPromoted =
        false
    ; terminalUnificationPromotedIsFalse =
        refl
    ; receiptBoundary =
        "This receipt drafts the Phase 1 commit and tag message only"
        ∷ "It does not commit, tag, clean the concurrent worktree, or promote any terminal claim"
        ∷ []
    }

phase1CommitReceiptDoesNotTag :
  tagCreatedHere canonicalPhase1CommitReceipt ≡ false
phase1CommitReceiptDoesNotTag =
  refl

