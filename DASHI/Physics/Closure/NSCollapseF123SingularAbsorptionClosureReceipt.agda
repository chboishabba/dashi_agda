module DASHI.Physics.Closure.NSCollapseF123SingularAbsorptionClosureReceipt where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- Fail-closed receipt for the F123 singular absorption closure criterion.
--
-- This module records the exact surface requested by the closure ledger:
--   F123 ~ -g12^-1 (lambda3-lambda1)|<omega,e2>|^2,
--   the ratio criterion |<omega,e2>|^2 <= C_ratio*g12^2,
--   the resulting O(g12) consequence,
--   the finite GD1 gap PDE minimum terms,
--   the constants needed to close collapseImpossible,
--   and the remaining blockers.
--
-- The receipt stays fail-closed: collapseImpossible = false and Clay = false.
-- No theorem promotion is claimed here.

listLength : {A : Set} → List A → Nat
listLength [] = zero
listLength (_ ∷ xs) = suc (listLength xs)

data NSCollapseF123SingularAbsorptionClosureStatus : Set where
  singularAbsorptionClosureReceiptRecorded :
    NSCollapseF123SingularAbsorptionClosureStatus

data NSCollapseF123SingularAbsorptionClosureStage : Set where
  f123AsymptoticRecorded :
    NSCollapseF123SingularAbsorptionClosureStage
  ratioCriterionRecorded :
    NSCollapseF123SingularAbsorptionClosureStage
  og12ConsequenceRecorded :
    NSCollapseF123SingularAbsorptionClosureStage
  gd1MinimumGapPDEMinimumTermsRecorded :
    NSCollapseF123SingularAbsorptionClosureStage
  closingConstantsRecorded :
    NSCollapseF123SingularAbsorptionClosureStage
  remainingBlockersRecorded :
    NSCollapseF123SingularAbsorptionClosureStage
  collapseImpossibleFalseRecorded :
    NSCollapseF123SingularAbsorptionClosureStage
  clayFalseRecorded :
    NSCollapseF123SingularAbsorptionClosureStage
  canonicalRecordProjectionRecorded :
    NSCollapseF123SingularAbsorptionClosureStage
  receiptBoundaryRecorded :
    NSCollapseF123SingularAbsorptionClosureStage

canonicalNSCollapseF123SingularAbsorptionClosureStages :
  List NSCollapseF123SingularAbsorptionClosureStage
canonicalNSCollapseF123SingularAbsorptionClosureStages =
  f123AsymptoticRecorded
  ∷ ratioCriterionRecorded
  ∷ og12ConsequenceRecorded
  ∷ gd1MinimumGapPDEMinimumTermsRecorded
  ∷ closingConstantsRecorded
  ∷ remainingBlockersRecorded
  ∷ collapseImpossibleFalseRecorded
  ∷ clayFalseRecorded
  ∷ canonicalRecordProjectionRecorded
  ∷ receiptBoundaryRecorded
  ∷ []

data NSCollapseF123SingularAbsorptionClosureBlocker : Set where
  ratioConstantOpen :
    NSCollapseF123SingularAbsorptionClosureBlocker
  absorptionConstantOpen :
    NSCollapseF123SingularAbsorptionClosureBlocker
  gd1GapConstantOpen :
    NSCollapseF123SingularAbsorptionClosureBlocker
  finiteMinimumTermConstantOpen :
    NSCollapseF123SingularAbsorptionClosureBlocker
  boundaryLiftConstantOpen :
    NSCollapseF123SingularAbsorptionClosureBlocker
  collapseImpossiblePromotionOpen :
    NSCollapseF123SingularAbsorptionClosureBlocker
  clayPromotionOpen :
    NSCollapseF123SingularAbsorptionClosureBlocker

canonicalNSCollapseF123SingularAbsorptionClosureBlockers :
  List NSCollapseF123SingularAbsorptionClosureBlocker
canonicalNSCollapseF123SingularAbsorptionClosureBlockers =
  ratioConstantOpen
  ∷ absorptionConstantOpen
  ∷ gd1GapConstantOpen
  ∷ finiteMinimumTermConstantOpen
  ∷ boundaryLiftConstantOpen
  ∷ collapseImpossiblePromotionOpen
  ∷ clayPromotionOpen
  ∷ []

canonicalNSCollapseF123SingularAbsorptionClosureConstants :
  List String
canonicalNSCollapseF123SingularAbsorptionClosureConstants =
  "C_ratio"
  ∷ "C_absorb"
  ∷ "C_GD1"
  ∷ "C_minGap"
  ∷ "C_boundaryLift"
  ∷ "C_F123"
  ∷ []

f123AsymptoticText : String
f123AsymptoticText =
  "F123 ~ -g12^-1 (lambda3-lambda1)|<omega,e2>|^2"

ratioCriterionText : String
ratioCriterionText =
  "ratio criterion: |<omega,e2>|^2 <= C_ratio*g12^2"

og12ConsequenceText : String
og12ConsequenceText =
  "resulting O(g12): ratio control turns the singular F123 term into an O(g12) bound"

gd1MinimumGapPDEMinimumTermsText : String
gd1MinimumGapPDEMinimumTermsText =
  "finite GD1 gap PDE minimum terms: lambda3-lambda1, |<omega,e2>|^2, g12^-1, C_ratio, C_absorb, C_GD1, C_minGap, C_boundaryLift, and the boundary lift residue remain finite under the recorded absorption route"

closingConstantsText : String
closingConstantsText =
  "constants needed to close collapseImpossible: C_ratio, C_absorb, C_GD1, C_minGap, C_boundaryLift, and C_F123"

remainingBlockersText : String
remainingBlockersText =
  "remaining blockers: the ratio constant, absorption constant, GD1 gap constant, finite minimum-term constant, boundary lift constant, collapseImpossible promotion, and Clay promotion remain open"

receiptBoundaryText : List String
receiptBoundaryText =
  "F123 singular absorption receipt is recorded as fail-closed"
  ∷ "F123 ~ -g12^-1 (lambda3-lambda1)|<omega,e2>|^2 is the target asymptotic line"
  ∷ "ratio criterion: |<omega,e2>|^2 <= C_ratio*g12^2"
  ∷ "ratio criterion implies the recorded O(g12) consequence"
  ∷ "finite GD1 gap PDE minimum terms are explicitly listed"
  ∷ "constants needed to close collapseImpossible are explicitly listed"
  ∷ "remaining blockers are explicitly listed"
  ∷ "collapseImpossible remains false"
  ∷ "Clay remains false"
  ∷ "record projections are opened public for downstream use"
  ∷ []

record NSCollapseF123SingularAbsorptionClosureReceipt : Setω where
  field
    status :
      NSCollapseF123SingularAbsorptionClosureStatus

    statusIsCanonical :
      status ≡ singularAbsorptionClosureReceiptRecorded

    stageLedger :
      List NSCollapseF123SingularAbsorptionClosureStage

    stageLedgerIsCanonical :
      stageLedger ≡ canonicalNSCollapseF123SingularAbsorptionClosureStages

    stageCount :
      Nat

    stageCountIsCanonical :
      stageCount ≡ listLength canonicalNSCollapseF123SingularAbsorptionClosureStages

    closingConstants :
      List String

    closingConstantsIsCanonical :
      closingConstants ≡ canonicalNSCollapseF123SingularAbsorptionClosureConstants

    closingConstantCount :
      Nat

    closingConstantCountIsCanonical :
      closingConstantCount ≡ listLength canonicalNSCollapseF123SingularAbsorptionClosureConstants

    blockerLedger :
      List NSCollapseF123SingularAbsorptionClosureBlocker

    blockerLedgerIsCanonical :
      blockerLedger ≡ canonicalNSCollapseF123SingularAbsorptionClosureBlockers

    blockerCount :
      Nat

    blockerCountIsCanonical :
      blockerCount ≡ listLength canonicalNSCollapseF123SingularAbsorptionClosureBlockers

    f123Asymptotic :
      String

    f123AsymptoticIsCanonical :
      f123Asymptotic ≡ f123AsymptoticText

    ratioCriterion :
      String

    ratioCriterionIsCanonical :
      ratioCriterion ≡ ratioCriterionText

    og12Consequence :
      String

    og12ConsequenceIsCanonical :
      og12Consequence ≡ og12ConsequenceText

    gd1MinimumGapPDEMinimumTerms :
      String

    gd1MinimumGapPDEMinimumTermsIsCanonical :
      gd1MinimumGapPDEMinimumTerms ≡ gd1MinimumGapPDEMinimumTermsText

    remainingBlockers :
      String

    remainingBlockersIsCanonical :
      remainingBlockers ≡ remainingBlockersText

    collapseImpossible :
      Bool

    collapseImpossibleIsFalse :
      collapseImpossible ≡ false

    clay :
      Bool

    clayIsFalse :
      clay ≡ false

    receiptBoundary :
      List String

    receiptBoundaryIsCanonical :
      receiptBoundary ≡ receiptBoundaryText

open NSCollapseF123SingularAbsorptionClosureReceipt public

canonicalNSCollapseF123SingularAbsorptionClosureReceipt :
  NSCollapseF123SingularAbsorptionClosureReceipt
canonicalNSCollapseF123SingularAbsorptionClosureReceipt =
  record
    { status =
        singularAbsorptionClosureReceiptRecorded
    ; statusIsCanonical =
        refl
    ; stageLedger =
        canonicalNSCollapseF123SingularAbsorptionClosureStages
    ; stageLedgerIsCanonical =
        refl
    ; stageCount =
        listLength canonicalNSCollapseF123SingularAbsorptionClosureStages
    ; stageCountIsCanonical =
        refl
    ; closingConstants =
        canonicalNSCollapseF123SingularAbsorptionClosureConstants
    ; closingConstantsIsCanonical =
        refl
    ; closingConstantCount =
        listLength canonicalNSCollapseF123SingularAbsorptionClosureConstants
    ; closingConstantCountIsCanonical =
        refl
    ; blockerLedger =
        canonicalNSCollapseF123SingularAbsorptionClosureBlockers
    ; blockerLedgerIsCanonical =
        refl
    ; blockerCount =
        listLength canonicalNSCollapseF123SingularAbsorptionClosureBlockers
    ; blockerCountIsCanonical =
        refl
    ; f123Asymptotic =
        f123AsymptoticText
    ; f123AsymptoticIsCanonical =
        refl
    ; ratioCriterion =
        ratioCriterionText
    ; ratioCriterionIsCanonical =
        refl
    ; og12Consequence =
        og12ConsequenceText
    ; og12ConsequenceIsCanonical =
        refl
    ; gd1MinimumGapPDEMinimumTerms =
        gd1MinimumGapPDEMinimumTermsText
    ; gd1MinimumGapPDEMinimumTermsIsCanonical =
        refl
    ; remainingBlockers =
        remainingBlockersText
    ; remainingBlockersIsCanonical =
        refl
    ; collapseImpossible =
        false
    ; collapseImpossibleIsFalse =
        refl
    ; clay =
        false
    ; clayIsFalse =
        refl
    ; receiptBoundary =
        receiptBoundaryText
    ; receiptBoundaryIsCanonical =
        refl
    }
