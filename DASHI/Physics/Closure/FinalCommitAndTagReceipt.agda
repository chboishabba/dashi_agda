module DASHI.Physics.Closure.FinalCommitAndTagReceipt where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

------------------------------------------------------------------------
-- C6 final commit and tag receipt.
--
-- The runtime git operations are performed by the manager after validation.
-- This receipt records the requested final protocol and keeps all terminal
-- and Clay/physical promotion claims false at receipt construction.

phase2FlowPreservationTagName : String
phase2FlowPreservationTagName =
  "phase2-ns-h118-v1"

phase2FlowPreservationCommitMessage : String
phase2FlowPreservationCommitMessage =
  "NS: H^{11/8} threshold identified as optimal for adjacent-only dissipation dominance. Clay NS conditionally reduced to one large-data contraction proof. YM: Shimura tower spatial refinement inhabited but hyperbolic geometry is new blocker; p-adic flat limit candidate. CKM: CP phase within PDG 1sigma. Correct A3 over-claim. NS H^{7/4} superseded by H^{11/8}."

phase2FlowPreservationAggregateCommand : String
phase2FlowPreservationAggregateCommand =
  "timeout 300s agda -i . -i DCHoTT-Agda -i cubical -l standard-library DASHI/Everything.agda"

phase2FlowPreservationPromotionScanCommand : String
phase2FlowPreservationPromotionScanCommand =
  "promotion scan: require no unguarded true-valued Clay, terminal, exact-SM, or physical-CKM promotion fields"

data FinalCommitAndTagStep : Set where
  runFocusedCReceiptAgda :
    FinalCommitAndTagStep

  runAggregateAgda :
    FinalCommitAndTagStep

  runPromotionScan :
    FinalCommitAndTagStep

  runDiffCheck :
    FinalCommitAndTagStep

  stageManagerCFlowPreservationFiles :
    FinalCommitAndTagStep

  createManagerCCommit :
    FinalCommitAndTagStep

  createPhase2FlowPreservationTag :
    FinalCommitAndTagStep

  pushBranchAndTag :
    FinalCommitAndTagStep

canonicalFinalCommitAndTagProtocol :
  List FinalCommitAndTagStep
canonicalFinalCommitAndTagProtocol =
  runFocusedCReceiptAgda
  ∷ runAggregateAgda
  ∷ runPromotionScan
  ∷ runDiffCheck
  ∷ stageManagerCFlowPreservationFiles
  ∷ createManagerCCommit
  ∷ createPhase2FlowPreservationTag
  ∷ pushBranchAndTag
  ∷ []

data FinalCommitAndTagPromotion : Set where

finalCommitAndTagPromotionImpossibleHere :
  FinalCommitAndTagPromotion →
  ⊥
finalCommitAndTagPromotionImpossibleHere ()

record FinalCommitAndTagReceipt : Setω where
  field
    protocol :
      List FinalCommitAndTagStep

    protocolIsCanonical :
      protocol ≡ canonicalFinalCommitAndTagProtocol

    aggregateCommand :
      String

    aggregateCommandIsCanonical :
      aggregateCommand ≡ phase2FlowPreservationAggregateCommand

    promotionScanCommand :
      String

    promotionScanCommandIsCanonical :
      promotionScanCommand ≡ phase2FlowPreservationPromotionScanCommand

    commitMessage :
      String

    commitMessageIsCanonical :
      commitMessage ≡ phase2FlowPreservationCommitMessage

    tagName :
      String

    tagNameIsCanonical :
      tagName ≡ phase2FlowPreservationTagName

    runtimeCommitExecutedHere :
      Bool

    runtimeCommitExecutedHereIsFalseAtReceiptConstruction :
      runtimeCommitExecutedHere ≡ false

    runtimeTagExecutedHere :
      Bool

    runtimeTagExecutedHereIsFalseAtReceiptConstruction :
      runtimeTagExecutedHere ≡ false

    runtimePushExecutedHere :
      Bool

    runtimePushExecutedHereIsFalseAtReceiptConstruction :
      runtimePushExecutedHere ≡ false

    clayYangMillsPromoted :
      Bool

    clayYangMillsPromotedIsFalse :
      clayYangMillsPromoted ≡ false

    clayNavierStokesPromoted :
      Bool

    clayNavierStokesPromotedIsFalse :
      clayNavierStokesPromoted ≡ false

    exactStandardModelPromoted :
      Bool

    exactStandardModelPromotedIsFalse :
      exactStandardModelPromoted ≡ false

    physicalCKMPromoted :
      Bool

    physicalCKMPromotedIsFalse :
      physicalCKMPromoted ≡ false

    terminalClaimPromoted :
      Bool

    terminalClaimPromotedIsFalse :
      terminalClaimPromoted ≡ false

    promotionFlags :
      List FinalCommitAndTagPromotion

    promotionFlagsAreEmpty :
      promotionFlags ≡ []

    receiptBoundary :
      List String

open FinalCommitAndTagReceipt public

canonicalFinalCommitAndTagReceipt :
  FinalCommitAndTagReceipt
canonicalFinalCommitAndTagReceipt =
  record
    { protocol =
        canonicalFinalCommitAndTagProtocol
    ; protocolIsCanonical =
        refl
    ; aggregateCommand =
        phase2FlowPreservationAggregateCommand
    ; aggregateCommandIsCanonical =
        refl
    ; promotionScanCommand =
        phase2FlowPreservationPromotionScanCommand
    ; promotionScanCommandIsCanonical =
        refl
    ; commitMessage =
        phase2FlowPreservationCommitMessage
    ; commitMessageIsCanonical =
        refl
    ; tagName =
        phase2FlowPreservationTagName
    ; tagNameIsCanonical =
        refl
    ; runtimeCommitExecutedHere =
        false
    ; runtimeCommitExecutedHereIsFalseAtReceiptConstruction =
        refl
    ; runtimeTagExecutedHere =
        false
    ; runtimeTagExecutedHereIsFalseAtReceiptConstruction =
        refl
    ; runtimePushExecutedHere =
        false
    ; runtimePushExecutedHereIsFalseAtReceiptConstruction =
        refl
    ; clayYangMillsPromoted =
        false
    ; clayYangMillsPromotedIsFalse =
        refl
    ; clayNavierStokesPromoted =
        false
    ; clayNavierStokesPromotedIsFalse =
        refl
    ; exactStandardModelPromoted =
        false
    ; exactStandardModelPromotedIsFalse =
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
        "C6 records the final validation, commit, tag, and push protocol"
        ∷ "Runtime git actions are false at receipt construction and executed externally by the manager"
        ∷ "The requested tag is phase2-flow-preservation-v1"
        ∷ "All Clay, exact-SM, physical-CKM, and terminal promotions remain false"
        ∷ []
    }

finalCommitAndTagKeepsClayFalse :
  clayYangMillsPromoted canonicalFinalCommitAndTagReceipt
  ≡
  false
finalCommitAndTagKeepsClayFalse =
  refl

finalCommitAndTagKeepsCKMFalse :
  physicalCKMPromoted canonicalFinalCommitAndTagReceipt
  ≡
  false
finalCommitAndTagKeepsCKMFalse =
  refl

finalCommitAndTagNoPromotion :
  FinalCommitAndTagPromotion →
  ⊥
finalCommitAndTagNoPromotion =
  finalCommitAndTagPromotionImpossibleHere
