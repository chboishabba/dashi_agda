module DASHI.Physics.Closure.FinalCorrectionCommitReceipt where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

------------------------------------------------------------------------
-- Final CKM correction commit receipt.
--
-- This receipt records the phase2-ckm-correction-v1 close-out protocol.
-- The runtime git operations are executed by the manager after validation.
-- It keeps all Clay, adèlic-density, Langlands-shortcut, and physical-CKM
-- promotion claims false.

phase2CKMCorrectionTagName : String
phase2CKMCorrectionTagName =
  "phase2-ckm-correction-v1"

phase2CKMCorrectionCommitMessage : String
phase2CKMCorrectionCommitMessage =
  "CKM correction: demote |Vcb| (pdgTautology, A=0.8086 is PDG input), demote gamma (D=-7 selection unproved), demote beta (inherits D=-7 uncertainty), demote alpha (tautological consequence). G7 formally blocked pending Gates A/B/C. Paper 6 scope revised: only lambda (GJ) and |Vub| (leading-order structural hypothesis) survive. Paper 8 does not depend on CKM sector. No Clay promotions. No adèlic density. No Langlands shortcut."

phase2CKMCorrectionAggregateCommand : String
phase2CKMCorrectionAggregateCommand =
  "timeout 300s agda -i . -i DCHoTT-Agda -i cubical -l standard-library DASHI/Everything.agda"

phase2CKMCorrectionTargetedScan : String
phase2CKMCorrectionTargetedScan =
  "scan for remaining carrierArithmetic labels on Vcb, gamma, beta, alpha in CKM receipts"

data CKMCorrectionCommitStep : Set where
  stageCorrectionReceipts :
    CKMCorrectionCommitStep

  stageEverythingImportHunk :
    CKMCorrectionCommitStep

  runFocusedAgdaChecks :
    CKMCorrectionCommitStep

  runAggregateAgdaCheck :
    CKMCorrectionCommitStep

  runTargetedCKMLabelScan :
    CKMCorrectionCommitStep

  runDiffCheck :
    CKMCorrectionCommitStep

  createCorrectionCommit :
    CKMCorrectionCommitStep

  createCorrectionTag :
    CKMCorrectionCommitStep

  pushBranchAndTag :
    CKMCorrectionCommitStep

canonicalCKMCorrectionCommitProtocol :
  List CKMCorrectionCommitStep
canonicalCKMCorrectionCommitProtocol =
  stageCorrectionReceipts
  ∷ stageEverythingImportHunk
  ∷ runFocusedAgdaChecks
  ∷ runAggregateAgdaCheck
  ∷ runTargetedCKMLabelScan
  ∷ runDiffCheck
  ∷ createCorrectionCommit
  ∷ createCorrectionTag
  ∷ pushBranchAndTag
  ∷ []

data CKMCorrectionPromotion : Set where

ckmCorrectionPromotionImpossibleHere :
  CKMCorrectionPromotion →
  ⊥
ckmCorrectionPromotionImpossibleHere ()

canonicalCKMCorrectionDemotions :
  List String
canonicalCKMCorrectionDemotions =
  "|Vcb| -> pdgTautology; A=0.8086 is PDG input"
  ∷ "gamma -> ungroundedStructuralHypothesis; D=-7 selection unproved"
  ∷ "beta -> inheritsDMinus7Uncertainty"
  ∷ "alpha -> tautologicalConsequence"
  ∷ []

canonicalCKMCorrectionBoundary :
  List String
canonicalCKMCorrectionBoundary =
  "phase2-ckm-correction-v1 stages five correction receipts plus this final receipt"
  ∷ "CKMFullHonestyReceipt and Paper6DraftCompleteReceipt are corrected in place"
  ∷ "G7 remains blocked pending Gates A, B, and C"
  ∷ "Paper 6 scope is lambda as Georgi-Jarlskog literature connection plus |Vub| leading-order hypothesis"
  ∷ "Paper 8 does not depend on the CKM sector"
  ∷ "No Clay promotion, no physical CKM promotion, no adèlic-density shortcut, and no Langlands shortcut is made"
  ∷ []

record FinalCorrectionCommitReceipt : Setω where
  field
    protocol :
      List CKMCorrectionCommitStep

    protocolIsCanonical :
      protocol ≡ canonicalCKMCorrectionCommitProtocol

    correctionTag :
      String

    correctionTagIsCanonical :
      correctionTag ≡ phase2CKMCorrectionTagName

    commitMessage :
      String

    commitMessageIsCanonical :
      commitMessage ≡ phase2CKMCorrectionCommitMessage

    aggregateCommand :
      String

    aggregateCommandIsCanonical :
      aggregateCommand ≡ phase2CKMCorrectionAggregateCommand

    targetedScan :
      String

    targetedScanIsCanonical :
      targetedScan ≡ phase2CKMCorrectionTargetedScan

    demotions :
      List String

    demotionsAreCanonical :
      demotions ≡ canonicalCKMCorrectionDemotions

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

    G7Blocked :
      Bool

    G7BlockedIsTrue :
      G7Blocked ≡ true

    paper6SupportsPaper8 :
      Bool

    paper6SupportsPaper8IsFalse :
      paper6SupportsPaper8 ≡ false

    paper8RestsOnNSAndYMOnly :
      Bool

    paper8RestsOnNSAndYMOnlyIsTrue :
      paper8RestsOnNSAndYMOnly ≡ true

    clayPromoted :
      Bool

    clayPromotedIsFalse :
      clayPromoted ≡ false

    physicalCKMPromoted :
      Bool

    physicalCKMPromotedIsFalse :
      physicalCKMPromoted ≡ false

    adelicDensityShortcutPromoted :
      Bool

    adelicDensityShortcutPromotedIsFalse :
      adelicDensityShortcutPromoted ≡ false

    langlandsShortcutPromoted :
      Bool

    langlandsShortcutPromotedIsFalse :
      langlandsShortcutPromoted ≡ false

    promotionFlags :
      List CKMCorrectionPromotion

    promotionFlagsAreEmpty :
      promotionFlags ≡ []

    receiptBoundary :
      List String

    receiptBoundaryIsCanonical :
      receiptBoundary ≡ canonicalCKMCorrectionBoundary

open FinalCorrectionCommitReceipt public

canonicalFinalCorrectionCommitReceipt :
  FinalCorrectionCommitReceipt
canonicalFinalCorrectionCommitReceipt =
  record
    { protocol =
        canonicalCKMCorrectionCommitProtocol
    ; protocolIsCanonical =
        refl
    ; correctionTag =
        phase2CKMCorrectionTagName
    ; correctionTagIsCanonical =
        refl
    ; commitMessage =
        phase2CKMCorrectionCommitMessage
    ; commitMessageIsCanonical =
        refl
    ; aggregateCommand =
        phase2CKMCorrectionAggregateCommand
    ; aggregateCommandIsCanonical =
        refl
    ; targetedScan =
        phase2CKMCorrectionTargetedScan
    ; targetedScanIsCanonical =
        refl
    ; demotions =
        canonicalCKMCorrectionDemotions
    ; demotionsAreCanonical =
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
    ; G7Blocked =
        true
    ; G7BlockedIsTrue =
        refl
    ; paper6SupportsPaper8 =
        false
    ; paper6SupportsPaper8IsFalse =
        refl
    ; paper8RestsOnNSAndYMOnly =
        true
    ; paper8RestsOnNSAndYMOnlyIsTrue =
        refl
    ; clayPromoted =
        false
    ; clayPromotedIsFalse =
        refl
    ; physicalCKMPromoted =
        false
    ; physicalCKMPromotedIsFalse =
        refl
    ; adelicDensityShortcutPromoted =
        false
    ; adelicDensityShortcutPromotedIsFalse =
        refl
    ; langlandsShortcutPromoted =
        false
    ; langlandsShortcutPromotedIsFalse =
        refl
    ; promotionFlags =
        []
    ; promotionFlagsAreEmpty =
        refl
    ; receiptBoundary =
        canonicalCKMCorrectionBoundary
    ; receiptBoundaryIsCanonical =
        refl
    }

finalCorrectionTagRecorded :
  correctionTag canonicalFinalCorrectionCommitReceipt
  ≡
  phase2CKMCorrectionTagName
finalCorrectionTagRecorded =
  refl

finalCorrectionKeepsG7Blocked :
  G7Blocked canonicalFinalCorrectionCommitReceipt ≡ true
finalCorrectionKeepsG7Blocked =
  refl

finalCorrectionKeepsPaper6OutOfPaper8 :
  paper6SupportsPaper8 canonicalFinalCorrectionCommitReceipt ≡ false
finalCorrectionKeepsPaper6OutOfPaper8 =
  refl

finalCorrectionNoPhysicalCKMPromotion :
  physicalCKMPromoted canonicalFinalCorrectionCommitReceipt ≡ false
finalCorrectionNoPhysicalCKMPromotion =
  refl

finalCorrectionNoPromotion :
  CKMCorrectionPromotion →
  ⊥
finalCorrectionNoPromotion =
  ckmCorrectionPromotionImpossibleHere
