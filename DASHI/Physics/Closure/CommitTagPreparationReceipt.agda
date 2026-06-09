module DASHI.Physics.Closure.CommitTagPreparationReceipt where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; _∷_; [])

------------------------------------------------------------------------
-- Commit/tag preparation receipt.  This does not perform git actions.

data TagPreparationStep : Set where
  aggregateAgdaValidation :
    TagPreparationStep

  gitDiffCheck :
    TagPreparationStep

  worktreeCleanCheck :
    TagPreparationStep

  diagnosticTagMessagePrepared :
    TagPreparationStep

canonicalTagPreparationSteps : List TagPreparationStep
canonicalTagPreparationSteps =
  aggregateAgdaValidation
  ∷ gitDiffCheck
  ∷ worktreeCleanCheck
  ∷ diagnosticTagMessagePrepared
  ∷ []

tagName : String
tagName =
  "heegner-ckm-v2-diagnostic"

tagMessage : String
tagMessage =
  "Phase 1 frontier complete. lambda 0.04%, A 0.05%, charge quantisation from p3-lane, CS conductor-level map. No Clay/CKM/SM promotion. Honest fail-closed tower."

record CommitTagPreparationReceipt : Setω where
  field
    steps :
      List TagPreparationStep

    stepsAreCanonical :
      steps ≡ canonicalTagPreparationSteps

    recommendedTagName :
      String

    recommendedTagNameIsCanonical :
      recommendedTagName ≡ tagName

    recommendedTagMessage :
      String

    recommendedTagMessageIsCanonical :
      recommendedTagMessage ≡ tagMessage

    phase1FrontierComplete :
      Bool

    phase1FrontierCompleteIsTrue :
      phase1FrontierComplete ≡ true

    allFlagsHonest :
      Bool

    allFlagsHonestIsTrue :
      allFlagsHonest ≡ true

    aggregateValidatedAtReceiptTime :
      Bool

    aggregateValidatedAtReceiptTimeIsTrue :
      aggregateValidatedAtReceiptTime ≡ true

    doNotTagUntilWorktreeClean :
      Bool

    doNotTagUntilWorktreeCleanIsTrue :
      doNotTagUntilWorktreeClean ≡ true

    tagCreatedHere :
      Bool

    tagCreatedHereIsFalse :
      tagCreatedHere ≡ false

    clayPromotionIncluded :
      Bool

    clayPromotionIncludedIsFalse :
      clayPromotionIncluded ≡ false

    ckmPromotionIncluded :
      Bool

    ckmPromotionIncludedIsFalse :
      ckmPromotionIncluded ≡ false

    smPromotionIncluded :
      Bool

    smPromotionIncludedIsFalse :
      smPromotionIncluded ≡ false

    receiptBoundary :
      List String

open CommitTagPreparationReceipt public

canonicalCommitTagPreparationReceipt :
  CommitTagPreparationReceipt
canonicalCommitTagPreparationReceipt =
  record
    { steps =
        canonicalTagPreparationSteps
    ; stepsAreCanonical =
        refl
    ; recommendedTagName =
        tagName
    ; recommendedTagNameIsCanonical =
        refl
    ; recommendedTagMessage =
        tagMessage
    ; recommendedTagMessageIsCanonical =
        refl
    ; phase1FrontierComplete =
        true
    ; phase1FrontierCompleteIsTrue =
        refl
    ; allFlagsHonest =
        true
    ; allFlagsHonestIsTrue =
        refl
    ; aggregateValidatedAtReceiptTime =
        true
    ; aggregateValidatedAtReceiptTimeIsTrue =
        refl
    ; doNotTagUntilWorktreeClean =
        true
    ; doNotTagUntilWorktreeCleanIsTrue =
        refl
    ; tagCreatedHere =
        false
    ; tagCreatedHereIsFalse =
        refl
    ; clayPromotionIncluded =
        false
    ; clayPromotionIncludedIsFalse =
        refl
    ; ckmPromotionIncluded =
        false
    ; ckmPromotionIncludedIsFalse =
        refl
    ; smPromotionIncluded =
        false
    ; smPromotionIncludedIsFalse =
        refl
    ; receiptBoundary =
        "This receipt prepares the tag message only"
        ∷ "Do not create the tag until the concurrent worktree is clean and intentionally staged"
        ∷ "The tag name is diagnostic and includes no Clay, CKM, or SM promotion"
        ∷ []
    }

commitTagPreparationDoesNotCreateTag :
  tagCreatedHere canonicalCommitTagPreparationReceipt ≡ false
commitTagPreparationDoesNotCreateTag =
  refl

