module DASHI.Analysis.RiemannG2PoleQuotientOffIntermediateAllowanceCompilerExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.String using (String)

import DASHI.Analysis.RiemannAristotlePoleQuotientOffOrdinateNearFarBidiExact as NearFar
import DASHI.Analysis.RiemannG2PoleQuotientOffAllowanceDirectCompilerExact as Direct
import DASHI.Analysis.RiemannG2PoleQuotientProducerAllowanceTargetExact as Payment
import DASHI.Analysis.RiemannAristotleFarTailCutoffSelectorExact as FarSelector

------------------------------------------------------------------------
-- FINAL OFF ALLOWANCE: INTERMEDIATE-ALLOWANCE FACTORISATION
--
-- The older rational near/far lane already uses the useful proof shape
--
--   B_far(J) <= epsilon
--   B_near(J) + epsilon <= A_off
--   --------------------------------
--   B_near(J) + B_far(J) <= A_off.
--
-- The authoritative final pole-quotient carrier is deliberately weaker than a
-- full preorder: it exposes transitivity and two-sided additive monotonicity,
-- but not reflexivity globally.  We therefore do NOT strengthen that carrier or
-- import a new algebra axiom.  The only self-order fact needed by this compiler
-- is paid explicitly at the concrete near budget.
------------------------------------------------------------------------

record IntermediateNearFarAllowanceFit
    (S : NearFar.OrderedAdditiveNearFarSurface)
    (d : NearFar.NearFarOffOrdinateBudget S)
    (assigned : NearFar.Scalar S) : Set where
  constructor intermediate-near-far-allowance-fit
  field
    intermediateFarAllowance : NearFar.Scalar S

    nearBudgetSelfOrder :
      NearFar._≤_ S
        (NearFar.nearBudget d)
        (NearFar.nearBudget d)

    farBudgetBelowIntermediateAllowance :
      NearFar._≤_ S
        (NearFar.farBudget d)
        intermediateFarAllowance

    nearBudgetPlusIntermediateBelowAssigned :
      NearFar._≤_ S
        (NearFar.add S
          (NearFar.nearBudget d)
          intermediateFarAllowance)
        assigned

open IntermediateNearFarAllowanceFit public

compiledNearPlusFarBelowAssigned :
  (S : NearFar.OrderedAdditiveNearFarSurface) →
  (d : NearFar.NearFarOffOrdinateBudget S) →
  (assigned : NearFar.Scalar S) →
  IntermediateNearFarAllowanceFit S d assigned →
  NearFar._≤_ S
    (NearFar.add S
      (NearFar.nearBudget d)
      (NearFar.farBudget d))
    assigned
compiledNearPlusFarBelowAssigned S d assigned fit =
  NearFar.≤-trans S
    (NearFar.addMonotone S
      (nearBudgetSelfOrder fit)
      (farBudgetBelowIntermediateAllowance fit))
    (nearBudgetPlusIntermediateBelowAssigned fit)

------------------------------------------------------------------------
-- Same final Off compiler, but with the joint budget field generated from the
-- intermediate allowance certificate rather than paid as one opaque theorem.
------------------------------------------------------------------------

record DirectPoleQuotientOffIntermediateAllowanceInput
    (S : NearFar.OrderedAdditiveNearFarSurface) : Set₁ where
  field
    Taper Cutoff : Set
    universalPoleQuotientTaper : Taper
    chosenCutoff : Cutoff

    CrossingCutoff : Cutoff → Set
    chosenCutoffCrosses : CrossingCutoff chosenCutoff

    OffResponse : Taper → NearFar.Scalar S
    OffBudget : Taper → NearFar.Scalar S

    nearFarAt : Cutoff → NearFar.NearFarOffOrdinateBudget S

    offResponseAtUniversalIsChosenNearFarFull :
      OffResponse universalPoleQuotientTaper
      ≡ NearFar.fullResponse (nearFarAt chosenCutoff)

    offBudgetAtUniversalIsChosenNearPlusFarBudget :
      OffBudget universalPoleQuotientTaper
      ≡ NearFar.add S
          (NearFar.nearBudget (nearFarAt chosenCutoff))
          (NearFar.farBudget (nearFarAt chosenCutoff))

    assignedOffAllowance : NearFar.Scalar S

    intermediateAllowanceFit :
      IntermediateNearFarAllowanceFit
        S
        (nearFarAt chosenCutoff)
        assignedOffAllowance

    sameLiteralPoleQuotientTaperAsFinalConsumer : Set
    sameLiteralPoleQuotientTaperAsFinalConsumerReceipt :
      sameLiteralPoleQuotientTaperAsFinalConsumer

    producerReference : String

open DirectPoleQuotientOffIntermediateAllowanceInput public

compileDirectPoleQuotientOffAllowanceInput :
  ∀ {S} →
  DirectPoleQuotientOffIntermediateAllowanceInput S →
  Direct.DirectPoleQuotientOffAllowanceInput S
compileDirectPoleQuotientOffAllowanceInput {S} input = record
  { Direct.Taper = Taper input
  ; Direct.Cutoff = Cutoff input
  ; Direct.universalPoleQuotientTaper = universalPoleQuotientTaper input
  ; Direct.chosenCutoff = chosenCutoff input
  ; Direct.CrossingCutoff = CrossingCutoff input
  ; Direct.chosenCutoffCrosses = chosenCutoffCrosses input
  ; Direct.OffResponse = OffResponse input
  ; Direct.OffBudget = OffBudget input
  ; Direct.nearFarAt = nearFarAt input
  ; Direct.offResponseAtUniversalIsChosenNearFarFull =
      offResponseAtUniversalIsChosenNearFarFull input
  ; Direct.offBudgetAtUniversalIsChosenNearPlusFarBudget =
      offBudgetAtUniversalIsChosenNearPlusFarBudget input
  ; Direct.assignedOffAllowance = assignedOffAllowance input
  ; Direct.chosenNearPlusFarBudgetBelowAssignedAllowance =
      compiledNearPlusFarBelowAssigned
        S
        (nearFarAt input (chosenCutoff input))
        (assignedOffAllowance input)
        (intermediateAllowanceFit input)
  ; Direct.sameLiteralPoleQuotientTaperAsFinalConsumer =
      sameLiteralPoleQuotientTaperAsFinalConsumer input
  ; Direct.sameLiteralPoleQuotientTaperAsFinalConsumerReceipt =
      sameLiteralPoleQuotientTaperAsFinalConsumerReceipt input
  ; Direct.producerReference = producerReference input
  }

compilePoleQuotientOffAllowancePaymentViaIntermediate :
  ∀ {S} →
  DirectPoleQuotientOffIntermediateAllowanceInput S →
  Payment.PoleQuotientOffAllowancePayment
compilePoleQuotientOffAllowancePaymentViaIntermediate input =
  Direct.compilePoleQuotientOffAllowancePayment
    (compileDirectPoleQuotientOffAllowanceInput input)

------------------------------------------------------------------------
-- Search / theorem boundary.
------------------------------------------------------------------------

record PoleQuotientOffIntermediateAllowanceBoundary : Set where
  constructor pole-quotient-off-intermediate-allowance-boundary
  field
    olderRationalAllowancePatternGeneralisedToFinalCarrier : Bool
    olderRationalAllowancePatternGeneralisedToFinalCarrierIsTrue :
      olderRationalAllowancePatternGeneralisedToFinalCarrier ≡ true

    finalCarrierStrengthenedWithGlobalReflexivityAxiom : Bool
    finalCarrierStrengthenedWithGlobalReflexivityAxiomIsFalse :
      finalCarrierStrengthenedWithGlobalReflexivityAxiom ≡ false

    concreteNearBudgetSelfOrderReceiptExplicit : Bool
    concreteNearBudgetSelfOrderReceiptExplicitIsTrue :
      concreteNearBudgetSelfOrderReceiptExplicit ≡ true

    jointNearPlusFarAllowanceFitIsFreshOpaqueLeaf : Bool
    jointNearPlusFarAllowanceFitIsFreshOpaqueLeafIsFalse :
      jointNearPlusFarAllowanceFitIsFreshOpaqueLeaf ≡ false

    farTailNeedsFreshAnalysis : Bool
    farTailNeedsFreshAnalysisIsFalse : farTailNeedsFreshAnalysis ≡ false

    commonCutoffStillRequired : Bool
    commonCutoffStillRequiredIsTrue : commonCutoffStillRequired ≡ true

    phaseSensitiveNearPlusIntermediateAllowanceStillOpen : Bool
    phaseSensitiveNearPlusIntermediateAllowanceStillOpenIsTrue :
      phaseSensitiveNearPlusIntermediateAllowanceStillOpen ≡ true

    finalOffAllowancePaymentClosed : Bool
    finalOffAllowancePaymentClosedIsFalse :
      finalOffAllowancePaymentClosed ≡ false

    rhDerived : Bool
    rhDerivedIsFalse : rhDerived ≡ false

    highestAlphaReading : String

canonicalPoleQuotientOffIntermediateAllowanceBoundary :
  PoleQuotientOffIntermediateAllowanceBoundary
canonicalPoleQuotientOffIntermediateAllowanceBoundary =
  pole-quotient-off-intermediate-allowance-boundary
    true refl
    false refl
    true refl
    false refl
    false refl
    true refl
    true refl
    false refl
    false refl
    "Factor the final same-cutoff Off allowance through an explicit intermediate far allowance epsilon. The generic compiler proves B_near(J)+B_far(J) <= A_off from one concrete near self-order receipt, B_far(J) <= epsilon, and B_near(J)+epsilon <= A_off. This reuses the older near/far allowance idea without strengthening the final weak ordered-additive carrier. The checked far-tail mechanism remains owned; the live analytic content is still phase-sensitive control of the finite near budget at the same chosen crossing cutoff, strong enough to leave the selected intermediate allowance. The final Off payment and RH remain open."

farTailOwnerStillSaysJointCutoffCompilerClosed :
  FarSelector.FarTailCutoffSelectorBoundary.jointNearFarCutoffCompilerClosed
    FarSelector.canonicalFarTailCutoffSelectorBoundary ≡ true
farTailOwnerStillSaysJointCutoffCompilerClosed = refl

farTailOwnerStillRejectsFarOnlyFinalCutoff :
  FarSelector.FarTailCutoffSelectorBoundary.farTailDecayAloneSelectsFinalJointCutoff
    FarSelector.canonicalFarTailCutoffSelectorBoundary ≡ false
farTailOwnerStillRejectsFarOnlyFinalCutoff = refl
