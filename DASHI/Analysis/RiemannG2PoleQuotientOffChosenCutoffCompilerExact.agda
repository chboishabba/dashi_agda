module DASHI.Analysis.RiemannG2PoleQuotientOffChosenCutoffCompilerExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.String using (String)

import DASHI.Analysis.RiemannAristotlePoleQuotientOffOrdinateNearFarBidiExact as NearFar
import DASHI.Analysis.RiemannAristotlePoleQuotientOffOrdinateBudgetTargetExact as Off
import DASHI.Analysis.RiemannG2PoleQuotientProducerAllowanceTargetExact as Payment
import DASHI.Analysis.RiemannG2PoleQuotientOffAllowanceDirectCompilerExact as Family

------------------------------------------------------------------------
-- FINAL OFF COMPILER AT ONE CHOSEN CUTOFF
--
-- The older direct compiler accepts
--
--   nearFarAt : Cutoff -> NearFarOffOrdinateBudget
--
-- but uses it only at chosenCutoff.  The final RH consumer therefore does not
-- require a near estimate at every cutoff.  This owner keeps exactly one budget
-- object at the one crossing cutoff actually consumed downstream.
------------------------------------------------------------------------

record ChosenCutoffPoleQuotientOffAllowanceInput
    (S : NearFar.OrderedAdditiveNearFarSurface) : Set₁ where
  field
    Taper Cutoff : Set
    universalPoleQuotientTaper : Taper
    chosenCutoff : Cutoff

    CrossingCutoff : Cutoff -> Set
    chosenCutoffCrosses : CrossingCutoff chosenCutoff

    OffResponse : Taper -> NearFar.Scalar S
    OffBudget : Taper -> NearFar.Scalar S

    chosenNearFarBudget : NearFar.NearFarOffOrdinateBudget S

    offResponseAtUniversalIsChosenFull :
      OffResponse universalPoleQuotientTaper
      ≡ NearFar.fullResponse chosenNearFarBudget

    offBudgetAtUniversalIsChosenCombinedBudget :
      OffBudget universalPoleQuotientTaper
      ≡ NearFar.add S
          (NearFar.nearBudget chosenNearFarBudget)
          (NearFar.farBudget chosenNearFarBudget)

    assignedOffAllowance : NearFar.Scalar S

    chosenCombinedBudgetBelowAssignedAllowance :
      NearFar._≤_ S
        (NearFar.add S
          (NearFar.nearBudget chosenNearFarBudget)
          (NearFar.farBudget chosenNearFarBudget))
        assignedOffAllowance

    sameLiteralPoleQuotientTaperAsFinalConsumer : Set
    sameLiteralPoleQuotientTaperAsFinalConsumerReceipt :
      sameLiteralPoleQuotientTaperAsFinalConsumer

    producerReference : String

open ChosenCutoffPoleQuotientOffAllowanceInput public

compiledUniversalOffUpper :
  forall {S} ->
  (input : ChosenCutoffPoleQuotientOffAllowanceInput S) ->
  NearFar._≤_ S
    (OffResponse input (universalPoleQuotientTaper input))
    (OffBudget input (universalPoleQuotientTaper input))
compiledUniversalOffUpper {S} input
  with offResponseAtUniversalIsChosenFull input
     | offBudgetAtUniversalIsChosenCombinedBudget input
... | refl | refl =
  NearFar.compiledOffOrdinateUpper S (chosenNearFarBudget input)

compiledOffBudgetFitsAssignedAllowance :
  forall {S} ->
  (input : ChosenCutoffPoleQuotientOffAllowanceInput S) ->
  NearFar._≤_ S
    (OffBudget input (universalPoleQuotientTaper input))
    (assignedOffAllowance input)
compiledOffBudgetFitsAssignedAllowance {S} input
  with offBudgetAtUniversalIsChosenCombinedBudget input
... | refl = chosenCombinedBudgetBelowAssignedAllowance input

compilePoleQuotientOffTarget :
  forall {S} ->
  ChosenCutoffPoleQuotientOffAllowanceInput S ->
  Off.PoleQuotientOffOrdinateBudgetTarget
compilePoleQuotientOffTarget {S} input =
  Off.pole-quotient-off-ordinate-budget-target
    (NearFar.Scalar S)
    (Taper input)
    (OffResponse input)
    (OffBudget input)
    (NearFar._≤_ S)
    (universalPoleQuotientTaper input)
    (compiledUniversalOffUpper input)

compilePoleQuotientOffAllowancePayment :
  forall {S} ->
  ChosenCutoffPoleQuotientOffAllowanceInput S ->
  Payment.PoleQuotientOffAllowancePayment
compilePoleQuotientOffAllowancePayment input = record
  { Payment.target = compilePoleQuotientOffTarget input
  ; Payment.assignedOffAllowance = assignedOffAllowance input
  ; Payment.offBudgetBelowAssignedAllowance =
      compiledOffBudgetFitsAssignedAllowance input
  ; Payment.crossingCutoffFeedsThisExactOffProducer =
      CrossingCutoff input (chosenCutoff input)
  ; Payment.crossingCutoffFeedsThisExactOffProducerReceipt =
      chosenCutoffCrosses input
  ; Payment.sameLiteralPoleQuotientTaperAsFinalConsumer =
      sameLiteralPoleQuotientTaperAsFinalConsumer input
  ; Payment.sameLiteralPoleQuotientTaperAsFinalConsumerReceipt =
      sameLiteralPoleQuotientTaperAsFinalConsumerReceipt input
  ; Payment.producerReference = producerReference input
  }

------------------------------------------------------------------------
-- Compatibility projection from the older all-cutoff family API.
------------------------------------------------------------------------

fromFamilyInput :
  forall {S} ->
  Family.DirectPoleQuotientOffAllowanceInput S ->
  ChosenCutoffPoleQuotientOffAllowanceInput S
fromFamilyInput input = record
  { Taper = Family.Taper input
  ; Cutoff = Family.Cutoff input
  ; universalPoleQuotientTaper = Family.universalPoleQuotientTaper input
  ; chosenCutoff = Family.chosenCutoff input
  ; CrossingCutoff = Family.CrossingCutoff input
  ; chosenCutoffCrosses = Family.chosenCutoffCrosses input
  ; OffResponse = Family.OffResponse input
  ; OffBudget = Family.OffBudget input
  ; chosenNearFarBudget =
      Family.nearFarAt input (Family.chosenCutoff input)
  ; offResponseAtUniversalIsChosenFull =
      Family.offResponseAtUniversalIsChosenNearFarFull input
  ; offBudgetAtUniversalIsChosenCombinedBudget =
      Family.offBudgetAtUniversalIsChosenNearPlusFarBudget input
  ; assignedOffAllowance = Family.assignedOffAllowance input
  ; chosenCombinedBudgetBelowAssignedAllowance =
      Family.chosenNearPlusFarBudgetBelowAssignedAllowance input
  ; sameLiteralPoleQuotientTaperAsFinalConsumer =
      Family.sameLiteralPoleQuotientTaperAsFinalConsumer input
  ; sameLiteralPoleQuotientTaperAsFinalConsumerReceipt =
      Family.sameLiteralPoleQuotientTaperAsFinalConsumerReceipt input
  ; producerReference = Family.producerReference input
  }

record ChosenCutoffOffCompilerBoundary : Set where
  constructor chosen-cutoff-off-compiler-boundary
  field
    allCutoffNearBudgetFamilyRequired : Bool
    allCutoffNearBudgetFamilyRequiredIsFalse :
      allCutoffNearBudgetFamilyRequired ≡ false

    oneChosenNearFarBudgetSufficient : Bool
    oneChosenNearFarBudgetSufficientIsTrue :
      oneChosenNearFarBudgetSufficient ≡ true

    olderFamilyInputProjectsToChosenInput : Bool
    olderFamilyInputProjectsToChosenInputIsTrue :
      olderFamilyInputProjectsToChosenInput ≡ true

    finalPaymentCompilerClosedConditionally : Bool
    finalPaymentCompilerClosedConditionallyIsTrue :
      finalPaymentCompilerClosedConditionally ≡ true

    rhDerived : Bool
    rhDerivedIsFalse : rhDerived ≡ false

    highestAlphaReading : String

canonicalChosenCutoffOffCompilerBoundary : ChosenCutoffOffCompilerBoundary
canonicalChosenCutoffOffCompilerBoundary =
  chosen-cutoff-off-compiler-boundary
    false refl
    true refl
    true refl
    true refl
    false refl
    "The final Off consumer uses exactly one near/far budget object at the chosen crossing cutoff. Do not require NearFarOffOrdinateBudget at every cutoff merely because the older compiler accepted a family; it only projected that family at chosenCutoff. The old family API remains a compatibility source and compiles to this smaller chosen-cutoff input. RH is not derived."
