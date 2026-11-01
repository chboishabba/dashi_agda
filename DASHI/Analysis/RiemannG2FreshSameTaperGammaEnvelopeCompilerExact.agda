module DASHI.Analysis.RiemannG2FreshSameTaperGammaEnvelopeCompilerExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.String using (String)

import DASHI.Analysis.RiemannAristotlePoleQuotientGammaBudgetTargetExact as Gamma
import DASHI.Analysis.RiemannG2PoleQuotientGammaAllowanceDirectCompilerExact as Direct
import DASHI.Analysis.RiemannG2PoleQuotientProducerAllowanceTargetExact as Payment

------------------------------------------------------------------------
-- FRESH SAME-TAPER GAMMA ENVELOPE -> FINAL GAMMA PAYMENT
--
-- Historical 8889 producer identity is not part of the final theorem interface.
-- Any independent theorem on the literal universal pole-quotient taper may
-- supply a GammaResponse/GammaBudget pair and its upper theorem directly.
------------------------------------------------------------------------

record FreshSameTaperGammaEnvelope : Set₁ where
  field
    Scalar Taper : Set
    _≤_ : Scalar → Scalar → Set

    gammaResponse : Taper → Scalar
    gammaEnvelope : Taper → Scalar
    universalPoleQuotientTaper : Taper

    gammaResponseBelowEnvelope :
      _≤_
        (gammaResponse universalPoleQuotientTaper)
        (gammaEnvelope universalPoleQuotientTaper)

    sameLiteralPoleQuotientTaperAsFinalConsumer : Set
    sameLiteralPoleQuotientTaperAsFinalConsumerReceipt :
      sameLiteralPoleQuotientTaperAsFinalConsumer

    envelopeReference : String

open FreshSameTaperGammaEnvelope public

compileFreshGammaBudgetTarget :
  FreshSameTaperGammaEnvelope → Gamma.PoleQuotientGammaBudgetTarget
compileFreshGammaBudgetTarget envelope = record
  { Gamma.Scalar = Scalar envelope
  ; Gamma.Taper = Taper envelope
  ; Gamma.GammaResponse = gammaResponse envelope
  ; Gamma.GammaBudget = gammaEnvelope envelope
  ; Gamma._≤_ = FreshSameTaperGammaEnvelope._≤_ envelope
  ; Gamma.universalPoleQuotientTaper = universalPoleQuotientTaper envelope
  ; Gamma.gammaResponseUpper = gammaResponseBelowEnvelope envelope
  }

record FreshSameTaperGammaAllowanceInput
    (envelope : FreshSameTaperGammaEnvelope) : Set₁ where
  private
    target = compileFreshGammaBudgetTarget envelope
  field
    assignedGammaAllowance : Gamma.Scalar target

    envelopeBelowAssignedAllowance :
      Gamma._≤_ target
        (Gamma.GammaBudget target (Gamma.universalPoleQuotientTaper target))
        assignedGammaAllowance

    allowanceReference : String

open FreshSameTaperGammaAllowanceInput public

compileDirectGammaAllowanceInput :
  (envelope : FreshSameTaperGammaEnvelope) →
  FreshSameTaperGammaAllowanceInput envelope →
  Direct.DirectPoleQuotientGammaAllowanceInput
compileDirectGammaAllowanceInput envelope input = record
  { Direct.target = compileFreshGammaBudgetTarget envelope
  ; Direct.assignedGammaAllowance = assignedGammaAllowance input
  ; Direct.gammaBudgetBelowAssignedAllowance = envelopeBelowAssignedAllowance input
  ; Direct.sameLiteralPoleQuotientTaperAsFinalConsumer =
      sameLiteralPoleQuotientTaperAsFinalConsumer envelope
  ; Direct.sameLiteralPoleQuotientTaperAsFinalConsumerReceipt =
      sameLiteralPoleQuotientTaperAsFinalConsumerReceipt envelope
  ; Direct.producerReference = allowanceReference input
  }

compileFreshSameTaperGammaAllowancePayment :
  (envelope : FreshSameTaperGammaEnvelope) →
  FreshSameTaperGammaAllowanceInput envelope →
  Payment.PoleQuotientGammaAllowancePayment
compileFreshSameTaperGammaAllowancePayment envelope input =
  Direct.compilePoleQuotientGammaAllowancePayment
    (compileDirectGammaAllowanceInput envelope input)

record FreshSameTaperGammaEnvelopeBoundary : Set where
  constructor fresh-same-taper-gamma-envelope-boundary
  field
    historical8889IdentityRequiredForFreshEnvelope : Bool
    historical8889IdentityRequiredForFreshEnvelopeIsFalse :
      historical8889IdentityRequiredForFreshEnvelope ≡ false

    historicalPrecisionLossLocalizationRequiredForFreshEnvelope : Bool
    historicalPrecisionLossLocalizationRequiredForFreshEnvelopeIsFalse :
      historicalPrecisionLossLocalizationRequiredForFreshEnvelope ≡ false

    sameLiteralFinalTaperStillRequired : Bool
    sameLiteralFinalTaperStillRequiredIsTrue :
      sameLiteralFinalTaperStillRequired ≡ true

    freshResponseUpperCompilesGammaTarget : Bool
    freshResponseUpperCompilesGammaTargetIsTrue :
      freshResponseUpperCompilesGammaTarget ≡ true

    freshEnvelopeAllowanceFitCompilesFinalPayment : Bool
    freshEnvelopeAllowanceFitCompilesFinalPaymentIsTrue :
      freshEnvelopeAllowanceFitCompilesFinalPayment ≡ true

    freshGammaEnvelopeInhabitedHere : Bool
    freshGammaEnvelopeInhabitedHereIsFalse :
      freshGammaEnvelopeInhabitedHere ≡ false

    finalGammaPaymentClosedHere : Bool
    finalGammaPaymentClosedHereIsFalse : finalGammaPaymentClosedHere ≡ false

    rhDerived : Bool
    rhDerivedIsFalse : rhDerived ≡ false

    highestAlphaReading : String

canonicalFreshSameTaperGammaEnvelopeBoundary :
  FreshSameTaperGammaEnvelopeBoundary
canonicalFreshSameTaperGammaEnvelopeBoundary =
  fresh-same-taper-gamma-envelope-boundary
    false refl
    false refl
    true refl
    true refl
    true refl
    false refl
    false refl
    false refl
    "A fresh Gamma proof does not need to identify or repair the historical 8889 producer. Supply one theorem-bearing envelope on the exact universal pole-quotient taper: GammaResponse(g_pole) <= B_Gamma(g_pole), then prove B_Gamma(g_pole) <= A_Gamma. The first theorem compiles PoleQuotientGammaBudgetTarget; the second compiles the final PoleQuotientGammaAllowancePayment. Historical source identity remains necessary only for claims about the old implementation. No fresh envelope is fabricated here and RH remains open."
