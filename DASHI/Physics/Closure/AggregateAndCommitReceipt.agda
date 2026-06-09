module DASHI.Physics.Closure.AggregateAndCommitReceipt where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Physics.Closure.Phase1CommitReceipt as Commit
import DASHI.Physics.Closure.SessionEndProtocolReceipt as Session
import DASHI.Physics.Closure.WorktreeCleanupReceipt as Cleanup

------------------------------------------------------------------------
-- Aggregate/session-end protocol boundary.
--
-- This receipt records the current shared dirty-worktree boundary and the
-- external aggregate/commit protocol.  It does not stage, commit, tag, clean,
-- reset, or otherwise mutate git state.

data AggregateAndCommitStep : Set where
  inspectDirtyWorktree :
    AggregateAndCommitStep

  runAggregateAgdaExternally :
    AggregateAndCommitStep

  runDiffCheckExternally :
    AggregateAndCommitStep

  parentReviewsExactPaths :
    AggregateAndCommitStep

  parentMayStageLater :
    AggregateAndCommitStep

  parentMayCommitLater :
    AggregateAndCommitStep

  parentMayTagLater :
    AggregateAndCommitStep

canonicalAggregateAndCommitSteps :
  List AggregateAndCommitStep
canonicalAggregateAndCommitSteps =
  inspectDirtyWorktree
  ∷ runAggregateAgdaExternally
  ∷ runDiffCheckExternally
  ∷ parentReviewsExactPaths
  ∷ parentMayStageLater
  ∷ parentMayCommitLater
  ∷ parentMayTagLater
  ∷ []

data AggregateAndCommitBlocker : Set where
  concurrentDirtyWorktree :
    AggregateAndCommitBlocker

  aggregateValidationMustBeRunAtSessionEnd :
    AggregateAndCommitBlocker

  exactPathReviewRequiredBeforeStaging :
    AggregateAndCommitBlocker

  parentDecisionRequiredBeforeCommitOrTag :
    AggregateAndCommitBlocker

canonicalAggregateAndCommitBlockers :
  List AggregateAndCommitBlocker
canonicalAggregateAndCommitBlockers =
  concurrentDirtyWorktree
  ∷ aggregateValidationMustBeRunAtSessionEnd
  ∷ exactPathReviewRequiredBeforeStaging
  ∷ parentDecisionRequiredBeforeCommitOrTag
  ∷ []

data AggregateAndCommitPromotion : Set where

aggregateAndCommitPromotionImpossibleHere :
  AggregateAndCommitPromotion →
  ⊥
aggregateAndCommitPromotionImpossibleHere ()

aggregateSessionEndStatement : String
aggregateSessionEndStatement =
  "Aggregate/session-end protocol receipt: current worktree is dirty with concurrent worker edits; aggregate validation and any staging, commit, or tag are external parent decisions, not actions executed here."

record AggregateAndCommitReceipt : Setω where
  field
    cleanupReceipt :
      Cleanup.WorktreeCleanupReceipt

    worktreeDirtyBoundary :
      Cleanup.currentWorktreeDirty cleanupReceipt ≡ true

    cleanupDoesNotStageHere :
      Cleanup.filesStagedHere cleanupReceipt ≡ false

    cleanupDoesNotCommitHere :
      Cleanup.commitCreatedHere cleanupReceipt ≡ false

    cleanupDoesNotTagHere :
      Cleanup.tagCreatedHere cleanupReceipt ≡ false

    sessionEndReceipt :
      Session.SessionEndProtocolReceipt

    sessionCommandsNotExecutedHere :
      Session.commandsExecutedHere sessionEndReceipt ≡ false

    sessionCommitNotCreatedHere :
      Session.commitCreatedHere sessionEndReceipt ≡ false

    sessionTagNotCreatedHere :
      Session.tagCreatedHere sessionEndReceipt ≡ false

    commitReceipt :
      Commit.Phase1CommitReceipt

    commitMessageOnly :
      Commit.commitCreatedHere commitReceipt ≡ false

    tagMessageOnly :
      Commit.tagCreatedHere commitReceipt ≡ false

    steps :
      List AggregateAndCommitStep

    stepsAreCanonical :
      steps ≡ canonicalAggregateAndCommitSteps

    blockers :
      List AggregateAndCommitBlocker

    blockersAreCanonical :
      blockers ≡ canonicalAggregateAndCommitBlockers

    aggregateCommandRecorded :
      String

    aggregateCommandIsSessionCommand :
      aggregateCommandRecorded ≡ Session.aggregateCommand

    aggregateCommandRunExternally :
      Bool

    aggregateCommandRunExternallyIsTrue :
      aggregateCommandRunExternally ≡ true

    aggregateCommandExecutedHere :
      Bool

    aggregateCommandExecutedHereIsFalse :
      aggregateCommandExecutedHere ≡ false

    currentDirtyWorktreeRecorded :
      Bool

    currentDirtyWorktreeRecordedIsTrue :
      currentDirtyWorktreeRecorded ≡ true

    filesStagedHere :
      Bool

    filesStagedHereIsFalse :
      filesStagedHere ≡ false

    commitExecutedHere :
      Bool

    commitExecutedHereIsFalse :
      commitExecutedHere ≡ false

    tagExecutedHere :
      Bool

    tagExecutedHereIsFalse :
      tagExecutedHere ≡ false

    parentDecisionRequiredForCommitTag :
      Bool

    parentDecisionRequiredForCommitTagIsTrue :
      parentDecisionRequiredForCommitTag ≡ true

    terminalPromotion :
      Bool

    terminalPromotionIsFalse :
      terminalPromotion ≡ false

    promotionFlags :
      List AggregateAndCommitPromotion

    promotionFlagsAreEmpty :
      promotionFlags ≡ []

    statement :
      String

    statementIsCanonical :
      statement ≡ aggregateSessionEndStatement

    receiptBoundary :
      List String

open AggregateAndCommitReceipt public

canonicalAggregateAndCommitReceipt :
  AggregateAndCommitReceipt
canonicalAggregateAndCommitReceipt =
  record
    { cleanupReceipt =
        Cleanup.canonicalWorktreeCleanupReceipt
    ; worktreeDirtyBoundary =
        refl
    ; cleanupDoesNotStageHere =
        Cleanup.worktreeCleanupDoesNotStageHere
    ; cleanupDoesNotCommitHere =
        Cleanup.worktreeCleanupDoesNotCommitHere
    ; cleanupDoesNotTagHere =
        Cleanup.worktreeCleanupDoesNotTagHere
    ; sessionEndReceipt =
        Session.canonicalSessionEndProtocolReceipt
    ; sessionCommandsNotExecutedHere =
        refl
    ; sessionCommitNotCreatedHere =
        Session.sessionEndProtocolDoesNotCommit
    ; sessionTagNotCreatedHere =
        refl
    ; commitReceipt =
        Commit.canonicalPhase1CommitReceipt
    ; commitMessageOnly =
        refl
    ; tagMessageOnly =
        Commit.phase1CommitReceiptDoesNotTag
    ; steps =
        canonicalAggregateAndCommitSteps
    ; stepsAreCanonical =
        refl
    ; blockers =
        canonicalAggregateAndCommitBlockers
    ; blockersAreCanonical =
        refl
    ; aggregateCommandRecorded =
        Session.aggregateCommand
    ; aggregateCommandIsSessionCommand =
        refl
    ; aggregateCommandRunExternally =
        true
    ; aggregateCommandRunExternallyIsTrue =
        refl
    ; aggregateCommandExecutedHere =
        false
    ; aggregateCommandExecutedHereIsFalse =
        refl
    ; currentDirtyWorktreeRecorded =
        true
    ; currentDirtyWorktreeRecordedIsTrue =
        refl
    ; filesStagedHere =
        false
    ; filesStagedHereIsFalse =
        refl
    ; commitExecutedHere =
        false
    ; commitExecutedHereIsFalse =
        refl
    ; tagExecutedHere =
        false
    ; tagExecutedHereIsFalse =
        refl
    ; parentDecisionRequiredForCommitTag =
        true
    ; parentDecisionRequiredForCommitTagIsTrue =
        refl
    ; terminalPromotion =
        false
    ; terminalPromotionIsFalse =
        refl
    ; promotionFlags =
        []
    ; promotionFlagsAreEmpty =
        refl
    ; statement =
        aggregateSessionEndStatement
    ; statementIsCanonical =
        refl
    ; receiptBoundary =
        "Current boundary: shared worktree is dirty with concurrent edits"
        ∷ "Aggregate Agda validation is recorded as an external session-end command"
        ∷ "No file is staged, no commit is created, and no tag is created by this receipt"
        ∷ "Parent review and explicit parent decision are required before later staging, commit, or tag"
        ∷ []
    }

aggregateAndCommitRecordsDirtyBoundary :
  currentDirtyWorktreeRecorded canonicalAggregateAndCommitReceipt ≡ true
aggregateAndCommitRecordsDirtyBoundary =
  refl

aggregateAndCommitDoesNotStage :
  filesStagedHere canonicalAggregateAndCommitReceipt ≡ false
aggregateAndCommitDoesNotStage =
  refl

aggregateAndCommitDoesNotCommit :
  commitExecutedHere canonicalAggregateAndCommitReceipt ≡ false
aggregateAndCommitDoesNotCommit =
  refl

aggregateAndCommitDoesNotTag :
  tagExecutedHere canonicalAggregateAndCommitReceipt ≡ false
aggregateAndCommitDoesNotTag =
  refl
