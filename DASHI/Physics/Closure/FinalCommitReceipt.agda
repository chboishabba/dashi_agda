module DASHI.Physics.Closure.FinalCommitReceipt where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

------------------------------------------------------------------------
-- Final commit receipt for the gauge-group/closure tranche.
--
-- The git operation is performed by the manager after aggregate validation.
-- This receipt records the intended protocol and keeps every terminal or
-- Clay-facing promotion false at receipt construction.

phase2GaugeGroupCommitMessage : String
phase2GaugeGroupCommitMessage =
  "U(1)Y from Hecke circle on X0(3). SU(2)-SU(3) decoupling from lepton-quark split (SET candidate). Anomaly cancellation inherited. VEV and NS vorticity honestly closed. Paper 6 and 8 draft sections complete."

phase2GaugeGroupTagName : String
phase2GaugeGroupTagName =
  "phase2-gauge-group-v1"

phase2GaugeGroupAggregateCommand : String
phase2GaugeGroupAggregateCommand =
  "timeout 300s agda -i . -i DCHoTT-Agda -i cubical -l standard-library DASHI/Everything.agda"

phase2GaugeGroupPromotionScanCommand : String
phase2GaugeGroupPromotionScanCommand =
  "promotion scan: require no unguarded true-valued Clay, terminal, exact-SM, or physical-CKM promotion fields"

data FinalCommitStep : Set where
  runFocusedReceiptAgda :
    FinalCommitStep

  runAggregateAgda :
    FinalCommitStep

  runPromotionScan :
    FinalCommitStep

  runDiffCheck :
    FinalCommitStep

  stageGaugeGroupTrancheFiles :
    FinalCommitStep

  createGaugeGroupCommit :
    FinalCommitStep

  createGaugeGroupTag :
    FinalCommitStep

  pushBranchAndTags :
    FinalCommitStep

canonicalFinalCommitProtocol :
  List FinalCommitStep
canonicalFinalCommitProtocol =
  runFocusedReceiptAgda
  ∷ runAggregateAgda
  ∷ runPromotionScan
  ∷ runDiffCheck
  ∷ stageGaugeGroupTrancheFiles
  ∷ createGaugeGroupCommit
  ∷ createGaugeGroupTag
  ∷ pushBranchAndTags
  ∷ []

data FinalCommitPromotion : Set where

finalCommitPromotionImpossibleHere :
  FinalCommitPromotion →
  ⊥
finalCommitPromotionImpossibleHere ()

record FinalCommitReceipt : Setω where
  field
    protocol :
      List FinalCommitStep

    protocolIsCanonical :
      protocol ≡ canonicalFinalCommitProtocol

    aggregateCommand :
      String

    aggregateCommandIsCanonical :
      aggregateCommand ≡ phase2GaugeGroupAggregateCommand

    promotionScanCommand :
      String

    promotionScanCommandIsCanonical :
      promotionScanCommand ≡ phase2GaugeGroupPromotionScanCommand

    commitMessage :
      String

    commitMessageIsCanonical :
      commitMessage ≡ phase2GaugeGroupCommitMessage

    tagName :
      String

    tagNameIsCanonical :
      tagName ≡ phase2GaugeGroupTagName

    runtimeCommitExecutedHere :
      Bool

    runtimeCommitExecutedHereIsFalseAtReceiptConstruction :
      runtimeCommitExecutedHere ≡ false

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

    gDHREqualsGSMPromoted :
      Bool

    gDHREqualsGSMPromotedIsFalse :
      gDHREqualsGSMPromoted ≡ false

    physicalCKMPromoted :
      Bool

    physicalCKMPromotedIsFalse :
      physicalCKMPromoted ≡ false

    terminalClaimPromoted :
      Bool

    terminalClaimPromotedIsFalse :
      terminalClaimPromoted ≡ false

    promotionFlags :
      List FinalCommitPromotion

    promotionFlagsAreEmpty :
      promotionFlags ≡ []

    receiptBoundary :
      List String

open FinalCommitReceipt public

canonicalFinalCommitReceipt :
  FinalCommitReceipt
canonicalFinalCommitReceipt =
  record
    { protocol =
        canonicalFinalCommitProtocol
    ; protocolIsCanonical =
        refl
    ; aggregateCommand =
        phase2GaugeGroupAggregateCommand
    ; aggregateCommandIsCanonical =
        refl
    ; promotionScanCommand =
        phase2GaugeGroupPromotionScanCommand
    ; promotionScanCommandIsCanonical =
        refl
    ; commitMessage =
        phase2GaugeGroupCommitMessage
    ; commitMessageIsCanonical =
        refl
    ; tagName =
        phase2GaugeGroupTagName
    ; tagNameIsCanonical =
        refl
    ; runtimeCommitExecutedHere =
        false
    ; runtimeCommitExecutedHereIsFalseAtReceiptConstruction =
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
    ; gDHREqualsGSMPromoted =
        false
    ; gDHREqualsGSMPromotedIsFalse =
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
        "Records the final gauge-group tranche commit/tag/push protocol"
        ∷ "The runtime commit and push are performed only after validation"
        ∷ "No exact SM, DHR=SM, CKM, Clay, or terminal promotion is made here"
        ∷ []
    }

finalCommitKeepsClayFalse :
  clayYangMillsPromoted canonicalFinalCommitReceipt ≡ false
finalCommitKeepsClayFalse =
  refl

finalCommitKeepsNSFalse :
  clayNavierStokesPromoted canonicalFinalCommitReceipt ≡ false
finalCommitKeepsNSFalse =
  refl

finalCommitKeepsTerminalFalse :
  terminalClaimPromoted canonicalFinalCommitReceipt ≡ false
finalCommitKeepsTerminalFalse =
  refl

finalCommitNoPromotion :
  FinalCommitPromotion →
  ⊥
finalCommitNoPromotion =
  finalCommitPromotionImpossibleHere
