module DASHI.Analysis.RiemannG2PoleQuotientOffAllowanceDirectCompilerExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.String using (String)

import DASHI.Analysis.RiemannAristotlePoleQuotientOffOrdinateNearFarBidiExact as NearFar
import DASHI.Analysis.RiemannAristotlePoleQuotientOffOrdinateBudgetTargetExact as Off
import DASHI.Analysis.RiemannG2PoleQuotientProducerAllowanceTargetExact as Payment

------------------------------------------------------------------------
-- DIRECT FINAL H_off COMPILER
--
-- The checked/generic cutoff lane already supplies the algebraic shape
--
--   full <= near + far
--   near <= B_near
--   far  <= B_far.
--
-- Therefore the final off allowance theorem need not be attacked as one opaque
-- inequality.  Once the actual universal-pole response/budget functions are
-- identified with that near/far package and
--
--   B_near + B_far <= A_off,
--
-- the final PoleQuotientOffAllowancePayment is compiler output.
------------------------------------------------------------------------

record DirectPoleQuotientOffAllowanceInput
    (S : NearFar.OrderedAdditiveNearFarSurface) : Set₁ where
  field
    Taper : Set
    universalPoleQuotientTaper : Taper

    OffResponse : Taper → NearFar.Scalar S
    OffBudget : Taper → NearFar.Scalar S

    nearFar : NearFar.NearFarOffOrdinateBudget S

    offResponseAtUniversalIsNearFarFull :
      OffResponse universalPoleQuotientTaper
      ≡ NearFar.fullResponse nearFar

    offBudgetAtUniversalIsNearPlusFarBudget :
      OffBudget universalPoleQuotientTaper
      ≡ NearFar.add S
          (NearFar.nearBudget nearFar)
          (NearFar.farBudget nearFar)

    assignedOffAllowance : NearFar.Scalar S

    nearPlusFarBudgetBelowAssignedAllowance :
      NearFar._≤_ S
        (NearFar.add S
          (NearFar.nearBudget nearFar)
          (NearFar.farBudget nearFar))
        assignedOffAllowance

    crossingCutoffFeedsThisExactOffProducer : Set
    crossingCutoffFeedsThisExactOffProducerReceipt :
      crossingCutoffFeedsThisExactOffProducer

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
  with offResponseAtUniversalIsNearFarFull input
     | offBudgetAtUniversalIsNearPlusFarBudget input
... | refl | refl = NearFar.compiledOffOrdinateUpper S (nearFar input)

compiledOffBudgetFitsAssignedAllowance :
  ∀ {S} →
  (input : DirectPoleQuotientOffAllowanceInput S) →
  NearFar._≤_ S
    (OffBudget input (universalPoleQuotientTaper input))
    (assignedOffAllowance input)
compiledOffBudgetFitsAssignedAllowance {S} input
  with offBudgetAtUniversalIsNearPlusFarBudget input
... | refl = nearPlusFarBudgetBelowAssignedAllowance input

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
      crossingCutoffFeedsThisExactOffProducer input
  ; Payment.crossingCutoffFeedsThisExactOffProducerReceipt =
      crossingCutoffFeedsThisExactOffProducerReceipt input
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
  proveFullOffBoundFromScratch
  reproveFarShell
  proveSignedNearBudget
  fitNearPlusOwnedFarIntoAssignedAllowance
  compileFinalOffAllowancePayment
  : OffAllowancePayment

data PaymentState : Set where
  live downstream pruned : PaymentState

paymentState : OffAllowancePayment → PaymentState
paymentState proveFullOffBoundFromScratch = pruned
paymentState reproveFarShell = pruned
paymentState proveSignedNearBudget = live
paymentState fitNearPlusOwnedFarIntoAssignedAllowance = live
paymentState compileFinalOffAllowancePayment = downstream

fullOffReproofPruned :
  paymentState proveFullOffBoundFromScratch ≡ pruned
fullOffReproofPruned = refl

farShellReproofPruned :
  paymentState reproveFarShell ≡ pruned
farShellReproofPruned = refl

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

    signedNearEvaluationRemainsAnalyticLeaf : Bool
    signedNearEvaluationRemainsAnalyticLeafIsTrue :
      signedNearEvaluationRemainsAnalyticLeaf ≡ true

    nearPlusFarMustFitAssignedAllowance : Bool
    nearPlusFarMustFitAssignedAllowanceIsTrue :
      nearPlusFarMustFitAssignedAllowance ≡ true

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
    true refl
    true refl
    true refl
    false refl
    "Do not prove H_off as one opaque theorem and do not reprove the checked far shell. On the exact universal pole-quotient taper, prove the finite signed near response admits B_near, combine it with the already-owned B_far so B_near + B_far <= the consumer-assigned A_off, and identify the literal full response/budget with the existing near/far package. PoleQuotientOffOrdinateBudgetTarget and PoleQuotientOffAllowancePayment then compile automatically. RH is not derived."
