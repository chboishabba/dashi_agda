module DASHI.Analysis.RiemannG2PoleQuotientOffAllowanceDirectCompilerExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.String using (String)

import DASHI.Analysis.RiemannAristotlePoleQuotientOffOrdinateNearFarBidiExact as NearFar
import DASHI.Analysis.RiemannAristotlePoleQuotientOffOrdinateBudgetTargetExact as Off
import DASHI.Analysis.RiemannG2PoleQuotientProducerAllowanceTargetExact as Payment
import DASHI.Analysis.RiemannAristotleFarTailCutoffSelectorExact as FarSelector

------------------------------------------------------------------------
-- DIRECT FINAL H_off COMPILER
--
-- The cutoff is a genuine producer coordinate.  Near and far pieces must be
-- evaluated at ONE common chosen cutoff; far-tail decay alone cannot choose the
-- final cutoff because enlarging J simultaneously changes the signed near core.
--
-- At the chosen crossing cutoff J, the existing near/far compiler supplies
--
--   D_off <= D_near(J) + D_far(J)
--         <= B_near(J) + B_far(J).
--
-- Once that same combined budget fits the downstream-assigned A_off, the final
-- PoleQuotientOffAllowancePayment is compiler output.
------------------------------------------------------------------------

record DirectPoleQuotientOffAllowanceInput
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

    chosenNearPlusFarBudgetBelowAssignedAllowance :
      NearFar._≤_ S
        (NearFar.add S
          (NearFar.nearBudget (nearFarAt chosenCutoff))
          (NearFar.farBudget (nearFarAt chosenCutoff)))
        assignedOffAllowance

    sameLiteralPoleQuotientTaperAsFinalConsumer : Set
    sameLiteralPoleQuotientTaperAsFinalConsumerReceipt :
      sameLiteralPoleQuotientTaperAsFinalConsumer

    producerReference : String

open DirectPoleQuotientOffAllowanceInput public

------------------------------------------------------------------------
-- Equality-local helpers.
------------------------------------------------------------------------

compiledUniversalOffUpper :
  ∀ {S} →
  (input : DirectPoleQuotientOffAllowanceInput S) →
  NearFar._≤_ S
    (OffResponse input (universalPoleQuotientTaper input))
    (OffBudget input (universalPoleQuotientTaper input))
compiledUniversalOffUpper {S} input
  with offResponseAtUniversalIsChosenNearFarFull input
     | offBudgetAtUniversalIsChosenNearPlusFarBudget input
... | refl | refl =
  NearFar.compiledOffOrdinateUpper S (nearFarAt input (chosenCutoff input))

compiledOffBudgetFitsAssignedAllowance :
  ∀ {S} →
  (input : DirectPoleQuotientOffAllowanceInput S) →
  NearFar._≤_ S
    (OffBudget input (universalPoleQuotientTaper input))
    (assignedOffAllowance input)
compiledOffBudgetFitsAssignedAllowance {S} input
  with offBudgetAtUniversalIsChosenNearPlusFarBudget input
... | refl = chosenNearPlusFarBudgetBelowAssignedAllowance input

------------------------------------------------------------------------
-- Existing target + final producer-facing payment.
------------------------------------------------------------------------

compilePoleQuotientOffTarget :
  ∀ {S} →
  DirectPoleQuotientOffAllowanceInput S →
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
  ∀ {S} →
  DirectPoleQuotientOffAllowanceInput S →
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
-- Search compression.
------------------------------------------------------------------------

data OffAllowancePayment : Set where
  proveFullOffBoundFromScratch : OffAllowancePayment
  reproveFarShell : OffAllowancePayment
  chooseFarCutoffIndependentlyOfNearCore : OffAllowancePayment
  proveSignedNearBudgetAtCommonCutoff : OffAllowancePayment
  fitChosenNearPlusOwnedFarIntoAssignedAllowance : OffAllowancePayment
  compileFinalOffAllowancePayment : OffAllowancePayment


data PaymentState : Set where
  live : PaymentState
  downstream : PaymentState
  pruned : PaymentState

paymentState : OffAllowancePayment → PaymentState
paymentState proveFullOffBoundFromScratch = pruned
paymentState reproveFarShell = pruned
paymentState chooseFarCutoffIndependentlyOfNearCore = pruned
paymentState proveSignedNearBudgetAtCommonCutoff = live
paymentState fitChosenNearPlusOwnedFarIntoAssignedAllowance = live
paymentState compileFinalOffAllowancePayment = downstream

fullOffReproofPruned :
  paymentState proveFullOffBoundFromScratch ≡ pruned
fullOffReproofPruned = refl

farShellReproofPruned :
  paymentState reproveFarShell ≡ pruned
farShellReproofPruned = refl

farOnlyCutoffSelectionPruned :
  paymentState chooseFarCutoffIndependentlyOfNearCore ≡ pruned
farOnlyCutoffSelectionPruned = refl

farTailOwnerAgreesJointCutoffRequired :
  FarSelector.FarTailCutoffSelectorBoundary.farTailDecayAloneSelectsFinalJointCutoff
    FarSelector.canonicalFarTailCutoffSelectorBoundary ≡ false
farTailOwnerAgreesJointCutoffRequired = refl

record PoleQuotientOffAllowanceDirectCompilerBoundary : Set where
  constructor pole-quotient-off-allowance-direct-compiler-boundary
  field
    fullOffAllowancePaymentIsOpaqueSingleLeaf : Bool
    fullOffAllowancePaymentIsOpaqueSingleLeafIsFalse :
      fullOffAllowancePaymentIsOpaqueSingleLeaf ≡ false

    nearFarCompilerAlreadyOwnsFullComposition : Bool
    nearFarCompilerAlreadyOwnsFullCompositionIsTrue :
      nearFarCompilerAlreadyOwnsFullComposition ≡ true

    farShellNeedsFreshAnalysis : Bool
    farShellNeedsFreshAnalysisIsFalse :
      farShellNeedsFreshAnalysis ≡ false

    farDecayAloneSelectsFinalCutoff : Bool
    farDecayAloneSelectsFinalCutoffIsFalse :
      farDecayAloneSelectsFinalCutoff ≡ false

    oneCommonCrossingCutoffRequired : Bool
    oneCommonCrossingCutoffRequiredIsTrue :
      oneCommonCrossingCutoffRequired ≡ true

    signedNearEvaluationAtCommonCutoffRemainsAnalyticLeaf : Bool
    signedNearEvaluationAtCommonCutoffRemainsAnalyticLeafIsTrue :
      signedNearEvaluationAtCommonCutoffRemainsAnalyticLeaf ≡ true

    chosenNearPlusFarMustFitAssignedAllowance : Bool
    chosenNearPlusFarMustFitAssignedAllowanceIsTrue :
      chosenNearPlusFarMustFitAssignedAllowance ≡ true

    finalOffTargetAndAllowancePaymentCompile : Bool
    finalOffTargetAndAllowancePaymentCompileIsTrue :
      finalOffTargetAndAllowancePaymentCompile ≡ true

    rhDerived : Bool
    rhDerivedIsFalse : rhDerived ≡ false

    highestAlphaReading : String

canonicalPoleQuotientOffAllowanceDirectCompilerBoundary :
  PoleQuotientOffAllowanceDirectCompilerBoundary
canonicalPoleQuotientOffAllowanceDirectCompilerBoundary =
  pole-quotient-off-allowance-direct-compiler-boundary
    false refl
    true refl
    false refl
    false refl
    true refl
    true refl
    true refl
    true refl
    false refl
    "Do not prove H_off as one opaque theorem, do not reprove the checked far shell, and do not choose J from far decay alone. Use one quarter-period crossing cutoff J for the exact universal pole-quotient near/far split. Prove the finite signed near response at that same J admits B_near(J), combine it with the owned B_far(J), and prove B_near(J) + B_far(J) <= the consumer-assigned A_off. PoleQuotientOffOrdinateBudgetTarget and PoleQuotientOffAllowancePayment then compile automatically. RH is not derived."
