module DASHI.Physics.Closure.WorktreeCommitReceipt where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Physics.Closure.AggregateAndCommitReceipt as Aggregate
import DASHI.Physics.Closure.SessionEndProtocolReceipt as Session
import DASHI.Physics.Closure.WorktreeCleanupReceipt as Cleanup

------------------------------------------------------------------------
-- Worktree commit receipt.
--
-- The user requested execution, but the shared worktree currently contains
-- many concurrent untracked/modified files.  This receipt therefore records
-- the exact commit/tag protocol and keeps the "executed here" booleans false
-- unless the parent process actually stages and commits after validation.

commitMessage : String
commitMessage =
  "Phase 1 complete. lambda 0.04%, A 0.05%, charge quantisation from Z/6, quark-lepton separation from conductor-level coprimality, no 4th generation from Heegner exhaustion, SM fermion count 48, deg23 base from T13 Hecke degree, zeta(Q(sqrt(21)))(-1)=1/3. All Clay/CKM/SM terminal flags false."

phase1DiagnosticTag : String
phase1DiagnosticTag =
  "heegner-ckm-v2-diagnostic"

promotionScanCommand : String
promotionScanCommand =
  "rg \"Promoted|terminalClaimPromoted|ClayPromoted|gDHREqualsGSMPromoted\" DASHI/Physics --glob '*.agda'"

gitDiffCheckCommand : String
gitDiffCheckCommand =
  "git diff --check"

gitStageCommand : String
gitStageCommand =
  "git add DASHI Docs status.md devlog.md"

gitCommitCommand : String
gitCommitCommand =
  "git commit -m \"Phase 1 complete: Heegner-CKM-v2-diagnostic\""

gitTagCommand : String
gitTagCommand =
  "git tag heegner-ckm-v2-diagnostic"

data WorktreeCommitProtocolStep : Set where
  runAggregate :
    WorktreeCommitProtocolStep

  runPromotionScan :
    WorktreeCommitProtocolStep

  runDiffCheck :
    WorktreeCommitProtocolStep

  reviewConcurrentWorktree :
    WorktreeCommitProtocolStep

  stageReviewedFiles :
    WorktreeCommitProtocolStep

  createCommit :
    WorktreeCommitProtocolStep

  createTag :
    WorktreeCommitProtocolStep

canonicalWorktreeCommitProtocol :
  List WorktreeCommitProtocolStep
canonicalWorktreeCommitProtocol =
  runAggregate
  ∷ runPromotionScan
  ∷ runDiffCheck
  ∷ reviewConcurrentWorktree
  ∷ stageReviewedFiles
  ∷ createCommit
  ∷ createTag
  ∷ []

data WorktreeCommitPromotion : Set where

worktreeCommitPromotionImpossibleHere :
  WorktreeCommitPromotion →
  ⊥
worktreeCommitPromotionImpossibleHere ()

record WorktreeCommitReceipt : Setω where
  field
    aggregateReceipt :
      Aggregate.AggregateAndCommitReceipt

    aggregateTerminalStillFalse :
      Aggregate.terminalPromotion aggregateReceipt ≡ false

    cleanupReceipt :
      Cleanup.WorktreeCleanupReceipt

    dirtyWorktreeRecorded :
      Cleanup.currentWorktreeDirty cleanupReceipt ≡ true

    sessionEndReceipt :
      Session.SessionEndProtocolReceipt

    sessionAggregateCommand :
      String

    sessionAggregateCommandIsCanonical :
      sessionAggregateCommand ≡ Session.aggregateCommand

    protocol :
      List WorktreeCommitProtocolStep

    protocolIsCanonical :
      protocol ≡ canonicalWorktreeCommitProtocol

    commitMessageRecorded :
      String

    commitMessageIsCanonical :
      commitMessageRecorded ≡ commitMessage

    tagNameRecorded :
      String

    tagNameRecordedIsCanonical :
      tagNameRecorded ≡ phase1DiagnosticTag

    promotionScanRecorded :
      String

    promotionScanRecordedIsCanonical :
      promotionScanRecorded ≡ promotionScanCommand

    diffCheckRecorded :
      String

    diffCheckRecordedIsCanonical :
      diffCheckRecorded ≡ gitDiffCheckCommand

    stageCommandRecorded :
      String

    stageCommandRecordedIsCanonical :
      stageCommandRecorded ≡ gitStageCommand

    commitCommandRecorded :
      String

    commitCommandRecordedIsCanonical :
      commitCommandRecorded ≡ gitCommitCommand

    tagCommandRecorded :
      String

    tagCommandRecordedIsCanonical :
      tagCommandRecorded ≡ gitTagCommand

    aggregateExecutedHere :
      Bool

    aggregateExecutedHereIsFalse :
      aggregateExecutedHere ≡ false

    filesStagedHere :
      Bool

    filesStagedHereIsFalse :
      filesStagedHere ≡ false

    commitCreatedHere :
      Bool

    commitCreatedHereIsFalse :
      commitCreatedHere ≡ false

    tagCreatedHere :
      Bool

    tagCreatedHereIsFalse :
      tagCreatedHere ≡ false

    terminalClaimPromoted :
      Bool

    terminalClaimPromotedIsFalse :
      terminalClaimPromoted ≡ false

    promotionFlags :
      List WorktreeCommitPromotion

    promotionFlagsAreEmpty :
      promotionFlags ≡ []

open WorktreeCommitReceipt public

canonicalWorktreeCommitReceipt :
  WorktreeCommitReceipt
canonicalWorktreeCommitReceipt =
  record
    { aggregateReceipt =
        Aggregate.canonicalAggregateAndCommitReceipt
    ; aggregateTerminalStillFalse =
        refl
    ; cleanupReceipt =
        Cleanup.canonicalWorktreeCleanupReceipt
    ; dirtyWorktreeRecorded =
        Cleanup.currentWorktreeDirtyIsTrue
          Cleanup.canonicalWorktreeCleanupReceipt
    ; sessionEndReceipt =
        Session.canonicalSessionEndProtocolReceipt
    ; sessionAggregateCommand =
        Session.aggregateCommand
    ; sessionAggregateCommandIsCanonical =
        refl
    ; protocol =
        canonicalWorktreeCommitProtocol
    ; protocolIsCanonical =
        refl
    ; commitMessageRecorded =
        commitMessage
    ; commitMessageIsCanonical =
        refl
    ; tagNameRecorded =
        phase1DiagnosticTag
    ; tagNameRecordedIsCanonical =
        refl
    ; promotionScanRecorded =
        promotionScanCommand
    ; promotionScanRecordedIsCanonical =
        refl
    ; diffCheckRecorded =
        gitDiffCheckCommand
    ; diffCheckRecordedIsCanonical =
        refl
    ; stageCommandRecorded =
        gitStageCommand
    ; stageCommandRecordedIsCanonical =
        refl
    ; commitCommandRecorded =
        gitCommitCommand
    ; commitCommandRecordedIsCanonical =
        refl
    ; tagCommandRecorded =
        gitTagCommand
    ; tagCommandRecordedIsCanonical =
        refl
    ; aggregateExecutedHere =
        false
    ; aggregateExecutedHereIsFalse =
        refl
    ; filesStagedHere =
        false
    ; filesStagedHereIsFalse =
        refl
    ; commitCreatedHere =
        false
    ; commitCreatedHereIsFalse =
        refl
    ; tagCreatedHere =
        false
    ; tagCreatedHereIsFalse =
        refl
    ; terminalClaimPromoted =
        false
    ; terminalClaimPromotedIsFalse =
        refl
    ; promotionFlags =
        []
    ; promotionFlagsAreEmpty =
        refl
    }

worktreeCommitReceiptNoTerminalPromotion :
  terminalClaimPromoted canonicalWorktreeCommitReceipt
  ≡
  false
worktreeCommitReceiptNoTerminalPromotion =
  terminalClaimPromotedIsFalse canonicalWorktreeCommitReceipt
