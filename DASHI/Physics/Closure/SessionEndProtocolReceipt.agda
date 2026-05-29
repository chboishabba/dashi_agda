module DASHI.Physics.Closure.SessionEndProtocolReceipt where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Physics.Closure.WorktreeCleanupReceipt as Cleanup

------------------------------------------------------------------------
-- Session-end protocol, recorded without executing git mutations.

data SessionEndProtocolStep : Set where
  finalAggregateAgdaPass :
    SessionEndProtocolStep

  finalPromotionScan :
    SessionEndProtocolStep

  finalDiffCheck :
    SessionEndProtocolStep

  stageReviewedFiles :
    SessionEndProtocolStep

  createPhase1Commit :
    SessionEndProtocolStep

  createDiagnosticTag :
    SessionEndProtocolStep

  recordCommitHash :
    SessionEndProtocolStep

canonicalSessionEndProtocolSteps : List SessionEndProtocolStep
canonicalSessionEndProtocolSteps =
  finalAggregateAgdaPass
  ∷ finalPromotionScan
  ∷ finalDiffCheck
  ∷ stageReviewedFiles
  ∷ createPhase1Commit
  ∷ createDiagnosticTag
  ∷ recordCommitHash
  ∷ []

aggregateCommand : String
aggregateCommand =
  "timeout 300s agda -i . -i DCHoTT-Agda -i cubical -l standard-library DASHI/Everything.agda"

promotionScanCommand : String
promotionScanCommand =
  "grep -r \"= true\" DASHI/Physics/ --include=\"*.agda\" | grep -v \"-- \""

diffCheckCommand : String
diffCheckCommand =
  "git diff --check"

commitCommand : String
commitCommand =
  "git commit -m \"Phase 1 complete: Heegner-CKM-v2-diagnostic\""

tagCommand : String
tagCommand =
  "git tag heegner-ckm-v2-diagnostic"

record SessionEndProtocolReceipt : Setω where
  field
    cleanupReceipt :
      Cleanup.WorktreeCleanupReceipt

    cleanupDoesNotCommitHere :
      Cleanup.commitCreatedHere cleanupReceipt ≡ false

    protocolSteps :
      List SessionEndProtocolStep

    protocolStepsAreCanonical :
      protocolSteps ≡ canonicalSessionEndProtocolSteps

    sessionEndProtocolRecorded :
      Bool

    sessionEndProtocolRecordedIsTrue :
      sessionEndProtocolRecorded ≡ true

    aggregateCommandRecorded :
      String

    aggregateCommandIsCanonical :
      aggregateCommandRecorded ≡ aggregateCommand

    promotionScanCommandRecorded :
      String

    promotionScanCommandIsCanonical :
      promotionScanCommandRecorded ≡ promotionScanCommand

    diffCheckCommandRecorded :
      String

    diffCheckCommandIsCanonical :
      diffCheckCommandRecorded ≡ diffCheckCommand

    commitCommandRecorded :
      String

    commitCommandIsCanonical :
      commitCommandRecorded ≡ commitCommand

    tagCommandRecorded :
      String

    tagCommandIsCanonical :
      tagCommandRecorded ≡ tagCommand

    commandsExecutedHere :
      Bool

    commandsExecutedHereIsFalse :
      commandsExecutedHere ≡ false

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

    nextSessionStart :
      List String

open SessionEndProtocolReceipt public

canonicalSessionEndProtocolReceipt : SessionEndProtocolReceipt
canonicalSessionEndProtocolReceipt =
  record
    { cleanupReceipt =
        Cleanup.canonicalWorktreeCleanupReceipt
    ; cleanupDoesNotCommitHere =
        Cleanup.worktreeCleanupDoesNotCommitHere
    ; protocolSteps =
        canonicalSessionEndProtocolSteps
    ; protocolStepsAreCanonical =
        refl
    ; sessionEndProtocolRecorded =
        true
    ; sessionEndProtocolRecordedIsTrue =
        refl
    ; aggregateCommandRecorded =
        aggregateCommand
    ; aggregateCommandIsCanonical =
        refl
    ; promotionScanCommandRecorded =
        promotionScanCommand
    ; promotionScanCommandIsCanonical =
        refl
    ; diffCheckCommandRecorded =
        diffCheckCommand
    ; diffCheckCommandIsCanonical =
        refl
    ; commitCommandRecorded =
        commitCommand
    ; commitCommandIsCanonical =
        refl
    ; tagCommandRecorded =
        tagCommand
    ; tagCommandIsCanonical =
        refl
    ; commandsExecutedHere =
        false
    ; commandsExecutedHereIsFalse =
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
    ; nextSessionStart =
        "zeta_Q(sqrt(21))(-1)=1/3 does not by tested natural normalisation recover deg23"
        ∷ "all-scale 2/3/5 wavelet orthogonality/frame proof remains open"
        ∷ "degree-28 Vub NLO correction still needs a carrier RG derivation"
        ∷ []
    }

sessionEndProtocolDoesNotCommit :
  commitCreatedHere canonicalSessionEndProtocolReceipt ≡ false
sessionEndProtocolDoesNotCommit =
  refl

sessionEndProtocolKeepsTerminalFalse :
  terminalClaimPromoted canonicalSessionEndProtocolReceipt ≡ false
sessionEndProtocolKeepsTerminalFalse =
  refl

