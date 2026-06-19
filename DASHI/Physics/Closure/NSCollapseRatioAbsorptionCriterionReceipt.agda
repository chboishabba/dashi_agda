module DASHI.Physics.Closure.NSCollapseRatioAbsorptionCriterionReceipt where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.String using (String)

import DASHI.Physics.Closure.NSCollapseBoundaryEnergyQGronwallReceipt
  as QRoute
import DASHI.Physics.Closure.NSCollapseBoundarySobolevLiftReceipt
  as SobolevLift

------------------------------------------------------------------------
-- Collapse ratio absorption criterion receipt.
--
-- This module records the target route
--
--   |<omega,e2>|^2 <= C*g12^2
--
-- and packages the downstream consequences as receipt text only:
--   F123 = O(g12),
--   finite GD1 gap minimum terms,
--   non-singular collapse evolution.
--
-- The prerequisite receipts are the Q(t) boundary-energy/Gronwall ledger
-- and the boundary Sobolev lift ledger.  The remaining open items are the
-- exact absorption constant and the regularity blockers, so the file stays
-- fail-closed with collapseImpossible = false.

listLength : {A : Set} → List A → Nat
listLength [] =
  zero
listLength (_ ∷ xs) =
  suc (listLength xs)

data NSCollapseRatioAbsorptionCriterionStatus : Set where
  ratioAbsorptionCriterionRecorded :
    NSCollapseRatioAbsorptionCriterionStatus

data NSCollapseRatioAbsorptionCriterionStage : Set where
  qBoundaryEnergyPrerequisiteRecorded :
    NSCollapseRatioAbsorptionCriterionStage
  boundarySobolevLiftPrerequisiteRecorded :
    NSCollapseRatioAbsorptionCriterionStage
  targetRatioCriterionRecorded :
    NSCollapseRatioAbsorptionCriterionStage
  f123Og12ConsequenceRecorded :
    NSCollapseRatioAbsorptionCriterionStage
  finiteGD1GapMinimumTermsRecorded :
    NSCollapseRatioAbsorptionCriterionStage
  nonsingularCollapseEvolutionRecorded :
    NSCollapseRatioAbsorptionCriterionStage
  remainingConstantsAndRegularityBlockersRecorded :
    NSCollapseRatioAbsorptionCriterionStage
  collapseImpossibleFalseRecorded :
    NSCollapseRatioAbsorptionCriterionStage

canonicalNSCollapseRatioAbsorptionCriterionStages :
  List NSCollapseRatioAbsorptionCriterionStage
canonicalNSCollapseRatioAbsorptionCriterionStages =
  qBoundaryEnergyPrerequisiteRecorded
  ∷ boundarySobolevLiftPrerequisiteRecorded
  ∷ targetRatioCriterionRecorded
  ∷ f123Og12ConsequenceRecorded
  ∷ finiteGD1GapMinimumTermsRecorded
  ∷ nonsingularCollapseEvolutionRecorded
  ∷ remainingConstantsAndRegularityBlockersRecorded
  ∷ collapseImpossibleFalseRecorded
  ∷ []

data NSCollapseRatioAbsorptionCriterionBlocker : Set where
  absorptionConstantOpen :
    NSCollapseRatioAbsorptionCriterionBlocker
  gd1MinimumGapConstantOpen :
    NSCollapseRatioAbsorptionCriterionBlocker
  boundaryRegularityOpen :
    NSCollapseRatioAbsorptionCriterionBlocker
  hsPersistenceOpen :
    NSCollapseRatioAbsorptionCriterionBlocker

canonicalNSCollapseRatioAbsorptionCriterionBlockers :
  List NSCollapseRatioAbsorptionCriterionBlocker
canonicalNSCollapseRatioAbsorptionCriterionBlockers =
  absorptionConstantOpen
  ∷ gd1MinimumGapConstantOpen
  ∷ boundaryRegularityOpen
  ∷ hsPersistenceOpen
  ∷ []

ratioAbsorptionCriterionText : String
ratioAbsorptionCriterionText =
  "|<omega,e2>|^2 <= C*g12^2"

f123Og12ConsequenceText : String
f123Og12ConsequenceText =
  "If |<omega,e2>|^2 <= C*g12^2 then F123 = O(g12)"

finiteGD1GapMinimumTermsText : String
finiteGD1GapMinimumTermsText =
  "finite GD1 gap minimum terms are recorded: the lambda3-lambda1 factor and the g12-weighted minimum-gap terms stay finite under the absorption route"

nonsingularCollapseEvolutionText : String
nonsingularCollapseEvolutionText =
  "non-singular collapse evolution is the intended downstream consequence of the absorbed F123 term"

remainingConstantsAndRegularityBlockersText : String
remainingConstantsAndRegularityBlockersText =
  "Remaining blockers: absorption constant C_abs and GD1 minimum-gap constant C_GD1 are open; boundary regularity and H^s persistence are open; the Q(t) and Sobolev lift receipts are prerequisites, not blockers."

ratioAbsorptionCriterionBoundaryText : List String
ratioAbsorptionCriterionBoundaryText =
  "Q(t) boundary-energy / Gronwall prerequisite is imported as a canonical receipt"
  ∷ "boundary Sobolev lift prerequisite is imported as a canonical receipt"
  ∷ "target criterion recorded: |<omega,e2>|^2 <= C*g12^2"
  ∷ "downstream consequence recorded: F123 = O(g12)"
  ∷ "finite GD1 gap minimum terms are recorded"
  ∷ "non-singular collapse evolution is the intended downstream route"
  ∷ "remaining blockers are the open absorption constant and regularity items"
  ∷ "collapseImpossible remains false"
  ∷ "Clay remains false"
  ∷ []

record NSCollapseRatioAbsorptionCriterionReceipt : Setω where
  field
    status :
      NSCollapseRatioAbsorptionCriterionStatus
    statusIsCanonical :
      status ≡ ratioAbsorptionCriterionRecorded

    stageLedger :
      List NSCollapseRatioAbsorptionCriterionStage
    stageLedgerIsCanonical :
      stageLedger ≡ canonicalNSCollapseRatioAbsorptionCriterionStages

    stageCount :
      Nat
    stageCountIsCanonical :
      stageCount ≡ listLength canonicalNSCollapseRatioAbsorptionCriterionStages

    qBoundaryEnergyReceipt :
      QRoute.NSCollapseBoundaryEnergyQGronwallReceipt
    qBoundaryEnergyReceiptIsCanonical :
      qBoundaryEnergyReceipt
      ≡ QRoute.canonicalNSCollapseBoundaryEnergyQGronwallReceipt

    boundarySobolevLiftReceipt :
      SobolevLift.NSCollapseBoundarySobolevLiftReceipt
    boundarySobolevLiftReceiptIsCanonical :
      boundarySobolevLiftReceipt
      ≡ SobolevLift.canonicalNSCollapseBoundarySobolevLiftReceipt

    ratioAbsorptionCriterion :
      String
    ratioAbsorptionCriterionIsCanonical :
      ratioAbsorptionCriterion ≡ ratioAbsorptionCriterionText

    f123Og12Consequence :
      String
    f123Og12ConsequenceIsCanonical :
      f123Og12Consequence ≡ f123Og12ConsequenceText

    finiteGD1GapMinimumTerms :
      String
    finiteGD1GapMinimumTermsIsCanonical :
      finiteGD1GapMinimumTerms ≡ finiteGD1GapMinimumTermsText

    nonsingularCollapseEvolution :
      String
    nonsingularCollapseEvolutionIsCanonical :
      nonsingularCollapseEvolution ≡ nonsingularCollapseEvolutionText

    nonsingularCollapseEvolutionRecordedFlag :
      Bool
    nonsingularCollapseEvolutionRecordedFlagIsTrue :
      nonsingularCollapseEvolutionRecordedFlag ≡ true

    remainingBlockers :
      List NSCollapseRatioAbsorptionCriterionBlocker
    remainingBlockersIsCanonical :
      remainingBlockers ≡ canonicalNSCollapseRatioAbsorptionCriterionBlockers

    blockerCount :
      Nat
    blockerCountIsCanonical :
      blockerCount ≡ listLength canonicalNSCollapseRatioAbsorptionCriterionBlockers

    remainingConstantsAndRegularityBlockers :
      String
    remainingConstantsAndRegularityBlockersIsCanonical :
      remainingConstantsAndRegularityBlockers
      ≡ remainingConstantsAndRegularityBlockersText

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
      receiptBoundary ≡ ratioAbsorptionCriterionBoundaryText

open NSCollapseRatioAbsorptionCriterionReceipt public

canonicalNSCollapseRatioAbsorptionCriterionReceipt :
  NSCollapseRatioAbsorptionCriterionReceipt
canonicalNSCollapseRatioAbsorptionCriterionReceipt =
  record
    { status =
        ratioAbsorptionCriterionRecorded
    ; statusIsCanonical =
        refl
    ; stageLedger =
        canonicalNSCollapseRatioAbsorptionCriterionStages
    ; stageLedgerIsCanonical =
        refl
    ; stageCount =
        listLength canonicalNSCollapseRatioAbsorptionCriterionStages
    ; stageCountIsCanonical =
        refl
    ; qBoundaryEnergyReceipt =
        QRoute.canonicalNSCollapseBoundaryEnergyQGronwallReceipt
    ; qBoundaryEnergyReceiptIsCanonical =
        refl
    ; boundarySobolevLiftReceipt =
        SobolevLift.canonicalNSCollapseBoundarySobolevLiftReceipt
    ; boundarySobolevLiftReceiptIsCanonical =
        refl
    ; ratioAbsorptionCriterion =
        ratioAbsorptionCriterionText
    ; ratioAbsorptionCriterionIsCanonical =
        refl
    ; f123Og12Consequence =
        f123Og12ConsequenceText
    ; f123Og12ConsequenceIsCanonical =
        refl
    ; finiteGD1GapMinimumTerms =
        finiteGD1GapMinimumTermsText
    ; finiteGD1GapMinimumTermsIsCanonical =
        refl
    ; nonsingularCollapseEvolution =
        nonsingularCollapseEvolutionText
    ; nonsingularCollapseEvolutionIsCanonical =
        refl
    ; nonsingularCollapseEvolutionRecordedFlag =
        true
    ; nonsingularCollapseEvolutionRecordedFlagIsTrue =
        refl
    ; remainingBlockers =
        canonicalNSCollapseRatioAbsorptionCriterionBlockers
    ; remainingBlockersIsCanonical =
        refl
    ; blockerCount =
        listLength canonicalNSCollapseRatioAbsorptionCriterionBlockers
    ; blockerCountIsCanonical =
        refl
    ; remainingConstantsAndRegularityBlockers =
        remainingConstantsAndRegularityBlockersText
    ; remainingConstantsAndRegularityBlockersIsCanonical =
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
        ratioAbsorptionCriterionBoundaryText
    ; receiptBoundaryIsCanonical =
        refl
    }

------------------------------------------------------------------------
-- Projections.

canonicalNSCollapseRatioAbsorptionCriterionReceiptStatus :
  status canonicalNSCollapseRatioAbsorptionCriterionReceipt
  ≡ ratioAbsorptionCriterionRecorded
canonicalNSCollapseRatioAbsorptionCriterionReceiptStatus =
  refl

canonicalNSCollapseRatioAbsorptionCriterionReceiptStageLedger :
  stageLedger canonicalNSCollapseRatioAbsorptionCriterionReceipt
  ≡ canonicalNSCollapseRatioAbsorptionCriterionStages
canonicalNSCollapseRatioAbsorptionCriterionReceiptStageLedger =
  refl

canonicalNSCollapseRatioAbsorptionCriterionReceiptStageCount :
  stageCount canonicalNSCollapseRatioAbsorptionCriterionReceipt
  ≡ listLength canonicalNSCollapseRatioAbsorptionCriterionStages
canonicalNSCollapseRatioAbsorptionCriterionReceiptStageCount =
  refl

canonicalNSCollapseRatioAbsorptionCriterionReceiptQBoundaryEnergyReceipt :
  qBoundaryEnergyReceipt canonicalNSCollapseRatioAbsorptionCriterionReceipt
  ≡ QRoute.canonicalNSCollapseBoundaryEnergyQGronwallReceipt
canonicalNSCollapseRatioAbsorptionCriterionReceiptQBoundaryEnergyReceipt =
  refl

canonicalNSCollapseRatioAbsorptionCriterionReceiptBoundarySobolevLiftReceipt :
  boundarySobolevLiftReceipt canonicalNSCollapseRatioAbsorptionCriterionReceipt
  ≡ SobolevLift.canonicalNSCollapseBoundarySobolevLiftReceipt
canonicalNSCollapseRatioAbsorptionCriterionReceiptBoundarySobolevLiftReceipt =
  refl

canonicalNSCollapseRatioAbsorptionCriterionReceiptRatioAbsorptionCriterion :
  ratioAbsorptionCriterion canonicalNSCollapseRatioAbsorptionCriterionReceipt
  ≡ ratioAbsorptionCriterionText
canonicalNSCollapseRatioAbsorptionCriterionReceiptRatioAbsorptionCriterion =
  refl

canonicalNSCollapseRatioAbsorptionCriterionReceiptF123Og12Consequence :
  f123Og12Consequence canonicalNSCollapseRatioAbsorptionCriterionReceipt
  ≡ f123Og12ConsequenceText
canonicalNSCollapseRatioAbsorptionCriterionReceiptF123Og12Consequence =
  refl

canonicalNSCollapseRatioAbsorptionCriterionReceiptFiniteGD1GapMinimumTerms :
  finiteGD1GapMinimumTerms canonicalNSCollapseRatioAbsorptionCriterionReceipt
  ≡ finiteGD1GapMinimumTermsText
canonicalNSCollapseRatioAbsorptionCriterionReceiptFiniteGD1GapMinimumTerms =
  refl

canonicalNSCollapseRatioAbsorptionCriterionReceiptNonsingularCollapseEvolution :
  nonsingularCollapseEvolution
    canonicalNSCollapseRatioAbsorptionCriterionReceipt
  ≡ nonsingularCollapseEvolutionText
canonicalNSCollapseRatioAbsorptionCriterionReceiptNonsingularCollapseEvolution =
  refl

canonicalNSCollapseRatioAbsorptionCriterionReceiptNonsingularCollapseEvolutionRecorded :
  nonsingularCollapseEvolutionRecordedFlag
    canonicalNSCollapseRatioAbsorptionCriterionReceipt
  ≡ true
canonicalNSCollapseRatioAbsorptionCriterionReceiptNonsingularCollapseEvolutionRecorded =
  refl

canonicalNSCollapseRatioAbsorptionCriterionReceiptRemainingBlockers :
  remainingBlockers canonicalNSCollapseRatioAbsorptionCriterionReceipt
  ≡ canonicalNSCollapseRatioAbsorptionCriterionBlockers
canonicalNSCollapseRatioAbsorptionCriterionReceiptRemainingBlockers =
  refl

canonicalNSCollapseRatioAbsorptionCriterionReceiptBlockerCount :
  blockerCount canonicalNSCollapseRatioAbsorptionCriterionReceipt
  ≡ listLength canonicalNSCollapseRatioAbsorptionCriterionBlockers
canonicalNSCollapseRatioAbsorptionCriterionReceiptBlockerCount =
  refl

canonicalNSCollapseRatioAbsorptionCriterionReceiptRemainingConstantsAndRegularityBlockers :
  remainingConstantsAndRegularityBlockers
    canonicalNSCollapseRatioAbsorptionCriterionReceipt
  ≡ remainingConstantsAndRegularityBlockersText
canonicalNSCollapseRatioAbsorptionCriterionReceiptRemainingConstantsAndRegularityBlockers =
  refl

canonicalNSCollapseRatioAbsorptionCriterionReceiptCollapseImpossible :
  collapseImpossible canonicalNSCollapseRatioAbsorptionCriterionReceipt
  ≡ false
canonicalNSCollapseRatioAbsorptionCriterionReceiptCollapseImpossible =
  refl

canonicalNSCollapseRatioAbsorptionCriterionReceiptClay :
  clay canonicalNSCollapseRatioAbsorptionCriterionReceipt ≡ false
canonicalNSCollapseRatioAbsorptionCriterionReceiptClay =
  refl

canonicalNSCollapseRatioAbsorptionCriterionReceiptBoundary :
  receiptBoundary canonicalNSCollapseRatioAbsorptionCriterionReceipt
  ≡ ratioAbsorptionCriterionBoundaryText
canonicalNSCollapseRatioAbsorptionCriterionReceiptBoundary =
  refl
