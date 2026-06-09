module DASHI.Physics.Closure.WorktreeCleanupReceipt where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; _∷_; [])

------------------------------------------------------------------------
-- Worktree cleanup governance receipt.
--
-- This receipt records a later, non-destructive cleanup/staging plan for the
-- shared Manager C worktree.  It does not run git cleanup commands, does not
-- stage files, does not commit, and does not create a tag.

data WorktreeCleanupStatus : Set where
  cleanupPlanRecordedNoGitMutation :
    WorktreeCleanupStatus

data FileClassToStage : Set where
  closureAgdaReceipts :
    FileClassToStage

  qftAgdaReceipts :
    FileClassToStage

  paperGovernanceDocs :
    FileClassToStage

  receiptIndexesAndChecklists :
    FileClassToStage

  validationScripts :
    FileClassToStage

  statusAndDevlogEntries :
    FileClassToStage

canonicalFileClassesToStage :
  List FileClassToStage
canonicalFileClassesToStage =
  closureAgdaReceipts
  ∷ qftAgdaReceipts
  ∷ paperGovernanceDocs
  ∷ receiptIndexesAndChecklists
  ∷ validationScripts
  ∷ statusAndDevlogEntries
  ∷ []

data FileClassToExclude : Set where
  localPlaywrightMcpCache :
    FileClassToExclude

  downloadedArchivesUnlessExplicitlyOwned :
    FileClassToExclude

  generatedBuildOutputsUnlessSubmissionArtifact :
    FileClassToExclude

  unrelatedWorkerFiles :
    FileClassToExclude

  unvalidatedScratchOutputs :
    FileClassToExclude

canonicalFileClassesToExclude :
  List FileClassToExclude
canonicalFileClassesToExclude =
  localPlaywrightMcpCache
  ∷ downloadedArchivesUnlessExplicitlyOwned
  ∷ generatedBuildOutputsUnlessSubmissionArtifact
  ∷ unrelatedWorkerFiles
  ∷ unvalidatedScratchOutputs
  ∷ []

data CleanupCommandClass : Set where
  inspectStatus :
    CleanupCommandClass

  inspectUntracked :
    CleanupCommandClass

  inspectWhitespace :
    CleanupCommandClass

  validateAggregate :
    CleanupCommandClass

  stageExactReviewedPaths :
    CleanupCommandClass

canonicalCleanupCommandClasses :
  List CleanupCommandClass
canonicalCleanupCommandClasses =
  inspectStatus
  ∷ inspectUntracked
  ∷ inspectWhitespace
  ∷ validateAggregate
  ∷ stageExactReviewedPaths
  ∷ []

statusCommand : String
statusCommand =
  "git status --short"

untrackedCommand : String
untrackedCommand =
  "git ls-files --others --exclude-standard"

diffCheckCommand : String
diffCheckCommand =
  "git diff --check"

aggregateValidationCommand : String
aggregateValidationCommand =
  "timeout 300s agda -i . -i DCHoTT-Agda -i cubical -l standard-library DASHI/Everything.agda"

stageAgdaCommand : String
stageAgdaCommand =
  "git add -- DASHI/Physics/Closure/*.agda DASHI/Physics/QFT/*.agda DASHI/Physics/Moonshine/*.agda DASHI/Everything.agda"

stageDocsCommand : String
stageDocsCommand =
  "git add -- Docs/*.md status.md devlog.md TODO.md"

stageScriptsCommand : String
stageScriptsCommand =
  "git add -- scripts/check_*.py scripts/data/*.json"

forbiddenCleanupCommand : String
forbiddenCleanupCommand =
  "do not run git clean, git reset, git checkout --, commit, or tag from this receipt"

record WorktreeCleanupReceipt : Setω where
  field
    status :
      WorktreeCleanupStatus

    fileClassesToStage :
      List FileClassToStage

    fileClassesToStageAreCanonical :
      fileClassesToStage ≡ canonicalFileClassesToStage

    fileClassesToExclude :
      List FileClassToExclude

    fileClassesToExcludeAreCanonical :
      fileClassesToExclude ≡ canonicalFileClassesToExclude

    cleanupCommandClasses :
      List CleanupCommandClass

    cleanupCommandClassesAreCanonical :
      cleanupCommandClasses ≡ canonicalCleanupCommandClasses

    currentWorktreeDirty :
      Bool

    currentWorktreeDirtyIsTrue :
      currentWorktreeDirty ≡ true

    commandsRecordedOnly :
      Bool

    commandsRecordedOnlyIsTrue :
      commandsRecordedOnly ≡ true

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

    destructiveCleanupAllowed :
      Bool

    destructiveCleanupAllowedIsFalse :
      destructiveCleanupAllowed ≡ false

    inspectStatusCommand :
      String

    inspectStatusCommandIsCanonical :
      inspectStatusCommand ≡ statusCommand

    inspectUntrackedCommand :
      String

    inspectUntrackedCommandIsCanonical :
      inspectUntrackedCommand ≡ untrackedCommand

    inspectWhitespaceCommand :
      String

    inspectWhitespaceCommandIsCanonical :
      inspectWhitespaceCommand ≡ diffCheckCommand

    aggregateValidationCommandRecorded :
      String

    aggregateValidationCommandIsCanonical :
      aggregateValidationCommandRecorded ≡ aggregateValidationCommand

    stageAgdaCommandRecorded :
      String

    stageAgdaCommandIsCanonical :
      stageAgdaCommandRecorded ≡ stageAgdaCommand

    stageDocsCommandRecorded :
      String

    stageDocsCommandIsCanonical :
      stageDocsCommandRecorded ≡ stageDocsCommand

    stageScriptsCommandRecorded :
      String

    stageScriptsCommandIsCanonical :
      stageScriptsCommandRecorded ≡ stageScriptsCommand

    forbiddenCleanupCommandRecorded :
      String

    forbiddenCleanupCommandIsCanonical :
      forbiddenCleanupCommandRecorded ≡ forbiddenCleanupCommand

    receiptBoundary :
      List String

open WorktreeCleanupReceipt public

canonicalWorktreeCleanupReceipt :
  WorktreeCleanupReceipt
canonicalWorktreeCleanupReceipt =
  record
    { status =
        cleanupPlanRecordedNoGitMutation
    ; fileClassesToStage =
        canonicalFileClassesToStage
    ; fileClassesToStageAreCanonical =
        refl
    ; fileClassesToExclude =
        canonicalFileClassesToExclude
    ; fileClassesToExcludeAreCanonical =
        refl
    ; cleanupCommandClasses =
        canonicalCleanupCommandClasses
    ; cleanupCommandClassesAreCanonical =
        refl
    ; currentWorktreeDirty =
        true
    ; currentWorktreeDirtyIsTrue =
        refl
    ; commandsRecordedOnly =
        true
    ; commandsRecordedOnlyIsTrue =
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
    ; destructiveCleanupAllowed =
        false
    ; destructiveCleanupAllowedIsFalse =
        refl
    ; inspectStatusCommand =
        statusCommand
    ; inspectStatusCommandIsCanonical =
        refl
    ; inspectUntrackedCommand =
        untrackedCommand
    ; inspectUntrackedCommandIsCanonical =
        refl
    ; inspectWhitespaceCommand =
        diffCheckCommand
    ; inspectWhitespaceCommandIsCanonical =
        refl
    ; aggregateValidationCommandRecorded =
        aggregateValidationCommand
    ; aggregateValidationCommandIsCanonical =
        refl
    ; stageAgdaCommandRecorded =
        stageAgdaCommand
    ; stageAgdaCommandIsCanonical =
        refl
    ; stageDocsCommandRecorded =
        stageDocsCommand
    ; stageDocsCommandIsCanonical =
        refl
    ; stageScriptsCommandRecorded =
        stageScriptsCommand
    ; stageScriptsCommandIsCanonical =
        refl
    ; forbiddenCleanupCommandRecorded =
        forbiddenCleanupCommand
    ; forbiddenCleanupCommandIsCanonical =
        refl
    ; receiptBoundary =
        "Governance-only cleanup plan; this receipt does not stage, commit, tag, clean, reset, or revert"
        ∷ "Stage only reviewed Agda receipts, governance docs, validation scripts, and status/devlog entries by exact path after owner review"
        ∷ "Exclude local caches such as .playwright-mcp, downloaded archives unless explicitly owned, generated build outputs unless required for submission, unrelated worker files, and scratch outputs"
        ∷ "Run inspection and validation commands before any intentional staging"
        ∷ "Do not create heegner-ckm-v2-diagnostic or any other tag until the worktree is intentionally staged and clean"
        ∷ []
    }

worktreeCleanupDoesNotStageHere :
  filesStagedHere canonicalWorktreeCleanupReceipt ≡ false
worktreeCleanupDoesNotStageHere =
  refl

worktreeCleanupDoesNotCommitHere :
  commitCreatedHere canonicalWorktreeCleanupReceipt ≡ false
worktreeCleanupDoesNotCommitHere =
  refl

worktreeCleanupDoesNotTagHere :
  tagCreatedHere canonicalWorktreeCleanupReceipt ≡ false
worktreeCleanupDoesNotTagHere =
  refl

worktreeCleanupForbidsDestructiveCleanup :
  destructiveCleanupAllowed canonicalWorktreeCleanupReceipt ≡ false
worktreeCleanupForbidsDestructiveCleanup =
  refl
