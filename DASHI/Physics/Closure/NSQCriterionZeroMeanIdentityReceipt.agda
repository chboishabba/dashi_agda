module DASHI.Physics.Closure.NSQCriterionZeroMeanIdentityReceipt where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

------------------------------------------------------------------------
-- Q-criterion zero-mean identity receipt on the three-torus.
--
-- This module is a fail-closed ledger for the classical Q-criterion on T^3.
-- It records the smooth incompressible carrier, the algebraic form of Qvel,
-- the zero-mean integral identity, the nontriviality caveat, and the
-- immediate sign-change consequence for Omega_K = {Qvel > 0} and its
-- complement at nontrivial times.  No theorem, promotion, or Clay claim is
-- discharged here.

listLength : {A : Set} → List A → Nat
listLength [] = zero
listLength (_ ∷ xs) = suc (listLength xs)

data NSQCriterionZeroMeanIdentityStatus : Set where
  qCriterionZeroMeanIdentityReceiptRecorded :
    NSQCriterionZeroMeanIdentityStatus

data NSQCriterionZeroMeanIdentityStage : Set where
  smoothIncompressibleT3FlowRecorded :
    NSQCriterionZeroMeanIdentityStage
  qvelFormulaRecorded :
    NSQCriterionZeroMeanIdentityStage
  zeroMeanIntegralRecorded :
    NSQCriterionZeroMeanIdentityStage
  nontrivialityCaveatRecorded :
    NSQCriterionZeroMeanIdentityStage
  signChangeConsequenceRecorded :
    NSQCriterionZeroMeanIdentityStage
  theoremFlagKeptFalseRecorded :
    NSQCriterionZeroMeanIdentityStage
  promotionFlagKeptFalseRecorded :
    NSQCriterionZeroMeanIdentityStage
  clayFlagKeptFalseRecorded :
    NSQCriterionZeroMeanIdentityStage

canonicalNSQCriterionZeroMeanIdentityStages :
  List NSQCriterionZeroMeanIdentityStage
canonicalNSQCriterionZeroMeanIdentityStages =
  smoothIncompressibleT3FlowRecorded
  ∷ qvelFormulaRecorded
  ∷ zeroMeanIntegralRecorded
  ∷ nontrivialityCaveatRecorded
  ∷ signChangeConsequenceRecorded
  ∷ theoremFlagKeptFalseRecorded
  ∷ promotionFlagKeptFalseRecorded
  ∷ clayFlagKeptFalseRecorded
  ∷ []

data NSQCriterionZeroMeanIdentityBlocker : Set where
  trivialFlowCaseStillOpen :
    NSQCriterionZeroMeanIdentityBlocker
  measureTheoreticSignChangeNotProved :
    NSQCriterionZeroMeanIdentityBlocker
  nontrivialTimesNeedSeparateJustification :
    NSQCriterionZeroMeanIdentityBlocker
  theoremPromotionGateKeptClosed :
    NSQCriterionZeroMeanIdentityBlocker
  clayGateKeptClosed :
    NSQCriterionZeroMeanIdentityBlocker

canonicalNSQCriterionZeroMeanIdentityBlockers :
  List NSQCriterionZeroMeanIdentityBlocker
canonicalNSQCriterionZeroMeanIdentityBlockers =
  trivialFlowCaseStillOpen
  ∷ measureTheoreticSignChangeNotProved
  ∷ nontrivialTimesNeedSeparateJustification
  ∷ theoremPromotionGateKeptClosed
  ∷ clayGateKeptClosed
  ∷ []

data NSQCriterionZeroMeanIdentityPromotion : Set where

nsQCriterionZeroMeanIdentityPromotionImpossibleHere :
  NSQCriterionZeroMeanIdentityPromotion →
  ⊥
nsQCriterionZeroMeanIdentityPromotionImpossibleHere ()

canonicalCarrierStatement : String
canonicalCarrierStatement =
  "Smooth incompressible flow on T^3 is the carrier recorded by this receipt."

canonicalQvelFormulaStatement : String
canonicalQvelFormulaStatement =
  "Qvel = 1/2(||Omega_ant||_F^2 - ||S||_F^2) = 1/4|omega|^2 - 1/2 tr(S^2)."

canonicalZeroMeanStatement : String
canonicalZeroMeanStatement =
  "For smooth incompressible flow on T^3, integral_{T^3} Qvel = 0."

canonicalNontrivialityCaveatStatement : String
canonicalNontrivialityCaveatStatement =
  "Nontriviality caveat: the sign-change route is recorded only away from the trivial zero-flow case."

canonicalSignChangeConsequenceStatement : String
canonicalSignChangeConsequenceStatement =
  "For nontrivial times, Omega_K = {Qvel > 0} and its complement both have positive measure."

canonicalBoundaryStatement : String
canonicalBoundaryStatement =
  "Fail-closed receipt: the zero-mean identity and sign-change consequence are recorded, but no theorem, promotion, or Clay claim is discharged here."

canonicalOStatement : String
canonicalOStatement =
  "O: Smooth incompressible T^3 flow and the Qvel carrier are recorded."

canonicalRStatement : String
canonicalRStatement =
  "R: Qvel = 1/2(||Omega_ant||_F^2 - ||S||_F^2) = 1/4|omega|^2 - 1/2 tr(S^2) is recorded."

canonicalCStatement : String
canonicalCStatement =
  "C: The zero-mean identity integral_{T^3} Qvel = 0 is recorded."

canonicalSStatement : String
canonicalSStatement =
  "S: For nontrivial times, Omega_K and its complement are both recorded as positive-measure sets."

canonicalLStatement : String
canonicalLStatement =
  "L: The nontriviality caveat is explicit; the trivial-flow case is not collapsed away."

canonicalPStatement : String
canonicalPStatement =
  "P: Promotion flags remain false and the promotion type is empty."

canonicalGStatement : String
canonicalGStatement =
  "G: Fail closed: the sign-change consequence is visible, but not promoted as a theorem here."

canonicalFStatement : String
canonicalFStatement =
  "F: The receipt stays local to the torus Q-criterion ledger and does not discharge the open proof obligations."

canonicalReceiptBoundaryText :
  List String
canonicalReceiptBoundaryText =
  "Smooth incompressible carrier on T^3 is recorded."
  ∷ "Qvel is recorded in the strain/vorticity form 1/2(||Omega_ant||_F^2 - ||S||_F^2) = 1/4|omega|^2 - 1/2 tr(S^2)."
  ∷ "The zero-mean identity integral_{T^3} Qvel = 0 is recorded."
  ∷ "The nontriviality caveat is explicit."
  ∷ "For nontrivial times, Omega_K = {Qvel > 0} and its complement are both recorded as positive-measure sets."
  ∷ "Theorem, promotion, and Clay flags remain false."
  ∷ []

record NSQCriterionZeroMeanIdentityReceipt : Setω where
  field
    status :
      NSQCriterionZeroMeanIdentityStatus
    statusIsCanonical :
      status ≡ qCriterionZeroMeanIdentityReceiptRecorded

    stageTrail :
      List NSQCriterionZeroMeanIdentityStage
    stageTrailIsCanonical :
      stageTrail ≡ canonicalNSQCriterionZeroMeanIdentityStages
    stageCount :
      Nat
    stageCountIsCanonical :
      stageCount ≡ listLength canonicalNSQCriterionZeroMeanIdentityStages

    blockerTrail :
      List NSQCriterionZeroMeanIdentityBlocker
    blockerTrailIsCanonical :
      blockerTrail ≡ canonicalNSQCriterionZeroMeanIdentityBlockers
    blockerCount :
      Nat
    blockerCountIsCanonical :
      blockerCount ≡ listLength canonicalNSQCriterionZeroMeanIdentityBlockers

    carrierStatement :
      String
    carrierStatementIsCanonical :
      carrierStatement ≡ canonicalCarrierStatement

    qvelFormulaStatement :
      String
    qvelFormulaStatementIsCanonical :
      qvelFormulaStatement ≡ canonicalQvelFormulaStatement

    zeroMeanStatement :
      String
    zeroMeanStatementIsCanonical :
      zeroMeanStatement ≡ canonicalZeroMeanStatement

    nontrivialityCaveatStatement :
      String
    nontrivialityCaveatStatementIsCanonical :
      nontrivialityCaveatStatement ≡ canonicalNontrivialityCaveatStatement

    signChangeConsequenceStatement :
      String
    signChangeConsequenceStatementIsCanonical :
      signChangeConsequenceStatement ≡ canonicalSignChangeConsequenceStatement

    theoremFlag :
      Bool
    theoremFlagIsFalse :
      theoremFlag ≡ false

    promotionFlag :
      Bool
    promotionFlagIsFalse :
      promotionFlag ≡ false

    clayFlag :
      Bool
    clayFlagIsFalse :
      clayFlag ≡ false

    oStatement :
      String
    oStatementIsCanonical :
      oStatement ≡ canonicalOStatement

    rStatement :
      String
    rStatementIsCanonical :
      rStatement ≡ canonicalRStatement

    cStatement :
      String
    cStatementIsCanonical :
      cStatement ≡ canonicalCStatement

    sStatement :
      String
    sStatementIsCanonical :
      sStatement ≡ canonicalSStatement

    lStatement :
      String
    lStatementIsCanonical :
      lStatement ≡ canonicalLStatement

    pStatement :
      String
    pStatementIsCanonical :
      pStatement ≡ canonicalPStatement

    gStatement :
      String
    gStatementIsCanonical :
      gStatement ≡ canonicalGStatement

    fStatement :
      String
    fStatementIsCanonical :
      fStatement ≡ canonicalFStatement

    receiptBoundaryText :
      List String
    receiptBoundaryTextIsCanonical :
      receiptBoundaryText ≡ canonicalReceiptBoundaryText

open NSQCriterionZeroMeanIdentityReceipt public

canonicalNSQCriterionZeroMeanIdentityReceipt :
  NSQCriterionZeroMeanIdentityReceipt
canonicalNSQCriterionZeroMeanIdentityReceipt =
  record
    { status =
        qCriterionZeroMeanIdentityReceiptRecorded
    ; statusIsCanonical =
        refl
    ; stageTrail =
        canonicalNSQCriterionZeroMeanIdentityStages
    ; stageTrailIsCanonical =
        refl
    ; stageCount =
        listLength canonicalNSQCriterionZeroMeanIdentityStages
    ; stageCountIsCanonical =
        refl
    ; blockerTrail =
        canonicalNSQCriterionZeroMeanIdentityBlockers
    ; blockerTrailIsCanonical =
        refl
    ; blockerCount =
        listLength canonicalNSQCriterionZeroMeanIdentityBlockers
    ; blockerCountIsCanonical =
        refl
    ; carrierStatement =
        canonicalCarrierStatement
    ; carrierStatementIsCanonical =
        refl
    ; qvelFormulaStatement =
        canonicalQvelFormulaStatement
    ; qvelFormulaStatementIsCanonical =
        refl
    ; zeroMeanStatement =
        canonicalZeroMeanStatement
    ; zeroMeanStatementIsCanonical =
        refl
    ; nontrivialityCaveatStatement =
        canonicalNontrivialityCaveatStatement
    ; nontrivialityCaveatStatementIsCanonical =
        refl
    ; signChangeConsequenceStatement =
        canonicalSignChangeConsequenceStatement
    ; signChangeConsequenceStatementIsCanonical =
        refl
    ; theoremFlag =
        false
    ; theoremFlagIsFalse =
        refl
    ; promotionFlag =
        false
    ; promotionFlagIsFalse =
        refl
    ; clayFlag =
        false
    ; clayFlagIsFalse =
        refl
    ; oStatement =
        canonicalOStatement
    ; oStatementIsCanonical =
        refl
    ; rStatement =
        canonicalRStatement
    ; rStatementIsCanonical =
        refl
    ; cStatement =
        canonicalCStatement
    ; cStatementIsCanonical =
        refl
    ; sStatement =
        canonicalSStatement
    ; sStatementIsCanonical =
        refl
    ; lStatement =
        canonicalLStatement
    ; lStatementIsCanonical =
        refl
    ; pStatement =
        canonicalPStatement
    ; pStatementIsCanonical =
        refl
    ; gStatement =
        canonicalGStatement
    ; gStatementIsCanonical =
        refl
    ; fStatement =
        canonicalFStatement
    ; fStatementIsCanonical =
        refl
    ; receiptBoundaryText =
        canonicalReceiptBoundaryText
    ; receiptBoundaryTextIsCanonical =
        refl
    }
