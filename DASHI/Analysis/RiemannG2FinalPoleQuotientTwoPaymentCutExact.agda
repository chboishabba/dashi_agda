module DASHI.Analysis.RiemannG2FinalPoleQuotientTwoPaymentCutExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.String using (String)

import DASHI.Analysis.RiemannG2PoleQuotientProducerAllowanceTargetExact as Payment
import DASHI.Analysis.RiemannAristotlePoleQuotientClusterMarginTargetExact as Cluster
import DASHI.Analysis.RiemannAristotlePoleQuotientSplitComplementBudgetExact as Split
import DASHI.Analysis.RiemannG2FinalSplitComplementOrderTransportCompilerExact as Final

------------------------------------------------------------------------
-- AUTHORITATIVE TWO-PAYMENT TERMINAL CUT
--
-- The final high-ordinate consumer does not independently consume the internal
-- proof steps used to manufacture an Off or Gamma allowance payment.
--
-- Producer-side decompositions may still prove, for example,
--
--   chosen finite-near upper
--   + near budget leaves the far allowance
--   --------------------------------------
--   PoleQuotientOffAllowancePayment
--
-- or
--
--   same-taper Gamma envelope
--   + Gamma envelope fits assigned allowance
--   ----------------------------------------
--   PoleQuotientGammaAllowancePayment.
--
-- But after those producer records exist, the terminal analytic interface has
-- exactly TWO theorem-bearing sockets: Off and Gamma. The final order/same-
-- object/cluster attachment is a downstream representation package, and the
-- contradiction is compiler output.
------------------------------------------------------------------------

record FinalPoleQuotientTwoPayments : Set₁ where
  constructor final-pole-quotient-two-payments
  field
    offPayment : Payment.PoleQuotientOffAllowancePayment
    gammaPayment : Payment.PoleQuotientGammaAllowancePayment
    paymentReference : String

open FinalPoleQuotientTwoPayments public

record FinalPoleQuotientTwoPaymentAttachment
    (payments : FinalPoleQuotientTwoPayments) : Set₁ where
  field
    surface : Split.OrderedAdditiveComplementSurface
    cluster : Cluster.PoleQuotientClusterMarginTarget
    transport :
      Final.FinalPoleQuotientOrderTransport
        surface
        (offPayment payments)
        (gammaPayment payments)
        cluster
    attachmentReference : String

open FinalPoleQuotientTwoPaymentAttachment public

compileFinalHighOrdinateContradiction :
  (payments : FinalPoleQuotientTwoPayments) ->
  FinalPoleQuotientTwoPaymentAttachment payments ->
  ⊥
compileFinalHighOrdinateContradiction payments attachment =
  Final.orderTransportContradiction
    (FinalPoleQuotientTwoPaymentAttachment.transport attachment)

------------------------------------------------------------------------
-- Search classification.
--
-- These names distinguish terminal proof sockets from producer-internal
-- factorisation coordinates. This does NOT claim that the internal analytic
-- work is already proved; it says only that it is not an additional consumer
-- obligation after its enclosing payment object has been constructed.
------------------------------------------------------------------------

data FinalAnalyticCoordinate : Set where
  chosenFiniteNearUpper : FinalAnalyticCoordinate
  chosenNearLeavesFarAllowance : FinalAnalyticCoordinate
  freshSameTaperGammaEnvelope : FinalAnalyticCoordinate
  gammaEnvelopeFitsAssignedAllowance : FinalAnalyticCoordinate
  offAllowancePayment : FinalAnalyticCoordinate
  gammaAllowancePayment : FinalAnalyticCoordinate
  finalOrderSameObjectClusterAttachment : FinalAnalyticCoordinate
  finalHighOrdinateContradiction : FinalAnalyticCoordinate


data TerminalRole : Set where
  producerInternal terminalAnalytic downstream compilerOutput : TerminalRole

terminalRole : FinalAnalyticCoordinate -> TerminalRole
terminalRole chosenFiniteNearUpper = producerInternal
terminalRole chosenNearLeavesFarAllowance = producerInternal
terminalRole freshSameTaperGammaEnvelope = producerInternal
terminalRole gammaEnvelopeFitsAssignedAllowance = producerInternal
terminalRole offAllowancePayment = terminalAnalytic
terminalRole gammaAllowancePayment = terminalAnalytic
terminalRole finalOrderSameObjectClusterAttachment = downstream
terminalRole finalHighOrdinateContradiction = compilerOutput

nearUpperNotIndependentTerminalSocket :
  terminalRole chosenFiniteNearUpper ≡ producerInternal
nearUpperNotIndependentTerminalSocket = refl

nearSlackNotIndependentTerminalSocket :
  terminalRole chosenNearLeavesFarAllowance ≡ producerInternal
nearSlackNotIndependentTerminalSocket = refl

gammaEnvelopeNotIndependentTerminalSocket :
  terminalRole freshSameTaperGammaEnvelope ≡ producerInternal
gammaEnvelopeNotIndependentTerminalSocket = refl

gammaFitNotIndependentTerminalSocket :
  terminalRole gammaEnvelopeFitsAssignedAllowance ≡ producerInternal
gammaFitNotIndependentTerminalSocket = refl

offPaymentIsTerminalAnalyticSocket :
  terminalRole offAllowancePayment ≡ terminalAnalytic
offPaymentIsTerminalAnalyticSocket = refl

gammaPaymentIsTerminalAnalyticSocket :
  terminalRole gammaAllowancePayment ≡ terminalAnalytic
gammaPaymentIsTerminalAnalyticSocket = refl

finalAttachmentIsDownstream :
  terminalRole finalOrderSameObjectClusterAttachment ≡ downstream
finalAttachmentIsDownstream = refl

finalContradictionIsCompilerOutput :
  terminalRole finalHighOrdinateContradiction ≡ compilerOutput
finalContradictionIsCompilerOutput = refl

record FinalPoleQuotientTwoPaymentBoundary : Set where
  constructor final-pole-quotient-two-payment-boundary
  field
    offAllowancePaymentIsTerminalAnalyticRequirement : Bool
    offAllowancePaymentIsTerminalAnalyticRequirementIsTrue :
      offAllowancePaymentIsTerminalAnalyticRequirement ≡ true

    gammaAllowancePaymentIsTerminalAnalyticRequirement : Bool
    gammaAllowancePaymentIsTerminalAnalyticRequirementIsTrue :
      gammaAllowancePaymentIsTerminalAnalyticRequirement ≡ true

    chosenNearUpperIsAdditionalTerminalRequirementAfterOffPayment : Bool
    chosenNearUpperIsAdditionalTerminalRequirementAfterOffPaymentIsFalse :
      chosenNearUpperIsAdditionalTerminalRequirementAfterOffPayment ≡ false

    chosenNearSlackIsAdditionalTerminalRequirementAfterOffPayment : Bool
    chosenNearSlackIsAdditionalTerminalRequirementAfterOffPaymentIsFalse :
      chosenNearSlackIsAdditionalTerminalRequirementAfterOffPayment ≡ false

    gammaEnvelopeIsAdditionalTerminalRequirementAfterGammaPayment : Bool
    gammaEnvelopeIsAdditionalTerminalRequirementAfterGammaPaymentIsFalse :
      gammaEnvelopeIsAdditionalTerminalRequirementAfterGammaPayment ≡ false

    gammaAllowanceFitIsAdditionalTerminalRequirementAfterGammaPayment : Bool
    gammaAllowanceFitIsAdditionalTerminalRequirementAfterGammaPaymentIsFalse :
      gammaAllowanceFitIsAdditionalTerminalRequirementAfterGammaPayment ≡ false

    finalOrderSameObjectClusterAttachmentIsFreshAnalyticPayment : Bool
    finalOrderSameObjectClusterAttachmentIsFreshAnalyticPaymentIsFalse :
      finalOrderSameObjectClusterAttachmentIsFreshAnalyticPayment ≡ false

    twoPaymentsPlusAttachmentCompileHighOrdinateContradiction : Bool
    twoPaymentsPlusAttachmentCompileHighOrdinateContradictionIsTrue :
      twoPaymentsPlusAttachmentCompileHighOrdinateContradiction ≡ true

    rhDerived : Bool
    rhDerivedIsFalse : rhDerived ≡ false

    highestAlphaReading : String

canonicalFinalPoleQuotientTwoPaymentBoundary :
  FinalPoleQuotientTwoPaymentBoundary
canonicalFinalPoleQuotientTwoPaymentBoundary =
  final-pole-quotient-two-payment-boundary
    true refl
    true refl
    false refl
    false refl
    false refl
    false refl
    false refl
    true refl
    false refl
    "At the authoritative final high-ordinate consumer boundary there are exactly two analytic payment sockets: PoleQuotientOffAllowancePayment and PoleQuotientGammaAllowancePayment. Chosen-near evaluation/slack and same-taper Gamma-envelope/fit remain legitimate producer-internal proof decompositions, but they are not four additional terminal obligations after the two payment records exist. The final order/same-object/cluster package is downstream representation work, and the existing order-transport compiler produces contradiction. This compression does not inhabit either analytic payment and does not derive RH."
