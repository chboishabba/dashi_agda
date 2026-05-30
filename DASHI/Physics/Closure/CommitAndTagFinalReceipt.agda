module DASHI.Physics.Closure.CommitAndTagFinalReceipt where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

------------------------------------------------------------------------
-- Final commit/tag execution receipt for the Phase 2 tranche.
--
-- The executable git operation is performed by the manager after aggregate
-- validation.  This receipt records the intended commit/tag protocol and
-- keeps all mathematical promotion flags false.

phase2CommitMessage : String
phase2CommitMessage =
  "Phase 2 initiated. Leray weak solution complete (NS W1-W5). YM L1-L3 partially inhabited via CS level running. CKM Yukawa normalisation identified as vol(X0(Nk))/sqrt(psi(Ni)*psi(Nj)). lambda 0.26%, Vcb 0.20%. All Clay/CKM terminal promotion flags false."

phase2TagName : String
phase2TagName =
  "phase2-clay-roadmap-v1"

phase2PromotionScanCommand : String
phase2PromotionScanCommand =
  "promotion scan: search true-valued Clay/terminal/physical-CKM fields and require no unguarded promotions"

phase2AggregateCommand : String
phase2AggregateCommand =
  "timeout 300s agda -i . -i DCHoTT-Agda -i cubical -l standard-library DASHI/Everything.agda"

data CommitAndTagFinalStep : Set where
  runFocusedAgda :
    CommitAndTagFinalStep

  runAggregateAgda :
    CommitAndTagFinalStep

  runPromotionScan :
    CommitAndTagFinalStep

  runDiffCheck :
    CommitAndTagFinalStep

  stagePhaseTwoFiles :
    CommitAndTagFinalStep

  createPhaseTwoCommit :
    CommitAndTagFinalStep

  createPhaseTwoTag :
    CommitAndTagFinalStep

canonicalCommitAndTagFinalProtocol :
  List CommitAndTagFinalStep
canonicalCommitAndTagFinalProtocol =
  runFocusedAgda
  ∷ runAggregateAgda
  ∷ runPromotionScan
  ∷ runDiffCheck
  ∷ stagePhaseTwoFiles
  ∷ createPhaseTwoCommit
  ∷ createPhaseTwoTag
  ∷ []

data CommitAndTagFinalPromotion : Set where

commitAndTagFinalPromotionImpossibleHere :
  CommitAndTagFinalPromotion →
  ⊥
commitAndTagFinalPromotionImpossibleHere ()

record CommitAndTagFinalReceipt : Setω where
  field
    protocol :
      List CommitAndTagFinalStep

    protocolIsCanonical :
      protocol ≡ canonicalCommitAndTagFinalProtocol

    protocolRecorded :
      Bool

    protocolRecordedIsTrue :
      protocolRecorded ≡ true

    aggregateCommand :
      String

    aggregateCommandIsCanonical :
      aggregateCommand ≡ phase2AggregateCommand

    promotionScanCommand :
      String

    promotionScanCommandIsCanonical :
      promotionScanCommand ≡ phase2PromotionScanCommand

    commitMessage :
      String

    commitMessageIsCanonical :
      commitMessage ≡ phase2CommitMessage

    tagName :
      String

    tagNameIsCanonical :
      tagName ≡ phase2TagName

    commitActuallyExecutedHere :
      Bool

    commitActuallyExecutedHereIsFalseAtReceiptConstruction :
      commitActuallyExecutedHere ≡ false

    tagActuallyExecutedHere :
      Bool

    tagActuallyExecutedHereIsFalseAtReceiptConstruction :
      tagActuallyExecutedHere ≡ false

    commitHashAvailable :
      Bool

    commitHashAvailableIsFalseAtReceiptConstruction :
      commitHashAvailable ≡ false

    clayYangMillsPromoted :
      Bool

    clayYangMillsPromotedIsFalse :
      clayYangMillsPromoted ≡ false

    clayNavierStokesPromoted :
      Bool

    clayNavierStokesPromotedIsFalse :
      clayNavierStokesPromoted ≡ false

    physicalCKMPromoted :
      Bool

    physicalCKMPromotedIsFalse :
      physicalCKMPromoted ≡ false

    terminalClaimPromoted :
      Bool

    terminalClaimPromotedIsFalse :
      terminalClaimPromoted ≡ false

    promotionFlags :
      List CommitAndTagFinalPromotion

    promotionFlagsAreEmpty :
      promotionFlags ≡ []

    receiptBoundary :
      List String

open CommitAndTagFinalReceipt public

canonicalCommitAndTagFinalReceipt :
  CommitAndTagFinalReceipt
canonicalCommitAndTagFinalReceipt =
  record
    { protocol =
        canonicalCommitAndTagFinalProtocol
    ; protocolIsCanonical =
        refl
    ; protocolRecorded =
        true
    ; protocolRecordedIsTrue =
        refl
    ; aggregateCommand =
        phase2AggregateCommand
    ; aggregateCommandIsCanonical =
        refl
    ; promotionScanCommand =
        phase2PromotionScanCommand
    ; promotionScanCommandIsCanonical =
        refl
    ; commitMessage =
        phase2CommitMessage
    ; commitMessageIsCanonical =
        refl
    ; tagName =
        phase2TagName
    ; tagNameIsCanonical =
        refl
    ; commitActuallyExecutedHere =
        false
    ; commitActuallyExecutedHereIsFalseAtReceiptConstruction =
        refl
    ; tagActuallyExecutedHere =
        false
    ; tagActuallyExecutedHereIsFalseAtReceiptConstruction =
        refl
    ; commitHashAvailable =
        false
    ; commitHashAvailableIsFalseAtReceiptConstruction =
        refl
    ; clayYangMillsPromoted =
        false
    ; clayYangMillsPromotedIsFalse =
        refl
    ; clayNavierStokesPromoted =
        false
    ; clayNavierStokesPromotedIsFalse =
        refl
    ; physicalCKMPromoted =
        false
    ; physicalCKMPromotedIsFalse =
        refl
    ; terminalClaimPromoted =
        false
    ; terminalClaimPromotedIsFalse =
        refl
    ; promotionFlags =
        []
    ; promotionFlagsAreEmpty =
        refl
    ; receiptBoundary =
        "The receipt records the Phase 2 commit/tag protocol before the manager executes git"
        ∷ "The runtime commit hash is intentionally reported by the manager after git commit"
        ∷ "No Clay, physical CKM, or terminal promotion follows from committing the tranche"
        ∷ []
    }

commitAndTagFinalKeepsTerminalFalse :
  terminalClaimPromoted canonicalCommitAndTagFinalReceipt ≡ false
commitAndTagFinalKeepsTerminalFalse =
  refl

commitAndTagFinalDoesNotCommit :
  commitActuallyExecutedHere canonicalCommitAndTagFinalReceipt ≡ false
commitAndTagFinalDoesNotCommit =
  refl

commitAndTagFinalDoesNotTag :
  tagActuallyExecutedHere canonicalCommitAndTagFinalReceipt ≡ false
commitAndTagFinalDoesNotTag =
  refl

commitAndTagFinalNoHashClaim :
  commitHashAvailable canonicalCommitAndTagFinalReceipt ≡ false
commitAndTagFinalNoHashClaim =
  refl

commitAndTagFinalNoPromotion :
  terminalClaimPromoted canonicalCommitAndTagFinalReceipt ≡ false
commitAndTagFinalNoPromotion =
  refl
