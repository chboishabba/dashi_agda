module DASHI.Physics.Closure.SessionEndReceipt where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Physics.Closure.CommitAndTagFinalReceipt as Commit
import DASHI.Physics.Closure.NSFinalStateReceipt as NS
import DASHI.Physics.Closure.SessionEndProtocolReceipt as Protocol
import DASHI.Physics.Closure.YMFinalStateReceipt as YM

------------------------------------------------------------------------
-- Session-end receipt state.

data ManagerCompletionState : Set where
  managerAComplete :
    ManagerCompletionState

  managerBComplete :
    ManagerCompletionState

  managerCComplete :
    ManagerCompletionState

  aggregateValidationReservedForManager :
    ManagerCompletionState

canonicalManagerCompletionStates :
  List ManagerCompletionState
canonicalManagerCompletionStates =
  managerAComplete
  ∷ managerBComplete
  ∷ managerCComplete
  ∷ aggregateValidationReservedForManager
  ∷ []

data SessionEndPromotion : Set where

sessionEndPromotionImpossibleHere :
  SessionEndPromotion →
  ⊥
sessionEndPromotionImpossibleHere ()

sessionEndStatement : String
sessionEndStatement =
  "Session end receipt records all managers complete as state only; no commit, tag, or commit hash is claimed here."

record SessionEndReceipt : Setω where
  field
    protocolReceipt :
      Protocol.SessionEndProtocolReceipt

    protocolDoesNotCommit :
      Protocol.commitCreatedHere protocolReceipt ≡ false

    protocolDoesNotTag :
      Protocol.tagCreatedHere protocolReceipt ≡ false

    nsFinalReceipt :
      NS.NSFinalStateReceipt

    nsFinalTerminalFalse :
      NS.terminalClaimPromoted nsFinalReceipt ≡ false

    ymFinalReceipt :
      YM.YMFinalStateReceipt

    ymFinalTerminalFalse :
      YM.terminalClayClaimPromoted ymFinalReceipt ≡ false

    commitAndTagReceipt :
      Commit.CommitAndTagFinalReceipt

    commitProtocolRecorded :
      Commit.protocolRecorded commitAndTagReceipt ≡ true

    commitNotExecuted :
      Commit.commitActuallyExecutedHere commitAndTagReceipt ≡ false

    tagNotExecuted :
      Commit.tagActuallyExecutedHere commitAndTagReceipt ≡ false

    commitHashNotAvailable :
      Commit.commitHashAvailable commitAndTagReceipt ≡ false

    managerStates :
      List ManagerCompletionState

    managerStatesAreCanonical :
      managerStates ≡ canonicalManagerCompletionStates

    allManagersCompleteRecorded :
      Bool

    allManagersCompleteRecordedIsTrue :
      allManagersCompleteRecorded ≡ true

    receiptStateOnly :
      Bool

    receiptStateOnlyIsTrue :
      receiptStateOnly ≡ true

    aggregateValidationExecutedHere :
      Bool

    aggregateValidationExecutedHereIsFalse :
      aggregateValidationExecutedHere ≡ false

    commitExecutedHere :
      Bool

    commitExecutedHereIsFalse :
      commitExecutedHere ≡ false

    tagExecutedHere :
      Bool

    tagExecutedHereIsFalse :
      tagExecutedHere ≡ false

    commitHashExistsHere :
      Bool

    commitHashExistsHereIsFalse :
      commitHashExistsHere ≡ false

    terminalClaimPromoted :
      Bool

    terminalClaimPromotedIsFalse :
      terminalClaimPromoted ≡ false

    promotionFlags :
      List SessionEndPromotion

    promotionFlagsAreEmpty :
      promotionFlags ≡ []

    statement :
      String

    statementIsCanonical :
      statement ≡ sessionEndStatement

    receiptBoundary :
      List String

open SessionEndReceipt public

canonicalSessionEndReceipt :
  SessionEndReceipt
canonicalSessionEndReceipt =
  record
    { protocolReceipt =
        Protocol.canonicalSessionEndProtocolReceipt
    ; protocolDoesNotCommit =
        refl
    ; protocolDoesNotTag =
        refl
    ; nsFinalReceipt =
        NS.canonicalNSFinalStateReceipt
    ; nsFinalTerminalFalse =
        refl
    ; ymFinalReceipt =
        YM.canonicalYMFinalStateReceipt
    ; ymFinalTerminalFalse =
        refl
    ; commitAndTagReceipt =
        Commit.canonicalCommitAndTagFinalReceipt
    ; commitProtocolRecorded =
        refl
    ; commitNotExecuted =
        refl
    ; tagNotExecuted =
        refl
    ; commitHashNotAvailable =
        refl
    ; managerStates =
        canonicalManagerCompletionStates
    ; managerStatesAreCanonical =
        refl
    ; allManagersCompleteRecorded =
        true
    ; allManagersCompleteRecordedIsTrue =
        refl
    ; receiptStateOnly =
        true
    ; receiptStateOnlyIsTrue =
        refl
    ; aggregateValidationExecutedHere =
        false
    ; aggregateValidationExecutedHereIsFalse =
        refl
    ; commitExecutedHere =
        false
    ; commitExecutedHereIsFalse =
        refl
    ; tagExecutedHere =
        false
    ; tagExecutedHereIsFalse =
        refl
    ; commitHashExistsHere =
        false
    ; commitHashExistsHereIsFalse =
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
        sessionEndStatement
    ; statementIsCanonical =
        refl
    ; receiptBoundary =
        "All managers complete is recorded as a receipt state, not as a git state"
        ∷ "No aggregate validation, commit, tag, or commit-hash capture is executed here"
        ∷ "Commit hash existence remains false because no commit was created by this worker"
        ∷ "NS, YM, commit/tag, and terminal promotion flags remain false"
        ∷ []
    }

sessionEndDoesNotCommit :
  commitExecutedHere canonicalSessionEndReceipt ≡ false
sessionEndDoesNotCommit =
  refl

sessionEndDoesNotClaimHash :
  commitHashExistsHere canonicalSessionEndReceipt ≡ false
sessionEndDoesNotClaimHash =
  refl

sessionEndKeepsTerminalFalse :
  terminalClaimPromoted canonicalSessionEndReceipt ≡ false
sessionEndKeepsTerminalFalse =
  refl

sessionEndNoPromotion :
  SessionEndPromotion →
  ⊥
sessionEndNoPromotion =
  sessionEndPromotionImpossibleHere
