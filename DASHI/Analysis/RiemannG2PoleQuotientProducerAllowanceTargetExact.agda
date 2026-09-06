module DASHI.Analysis.RiemannG2PoleQuotientProducerAllowanceTargetExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.String using (String)

import DASHI.Analysis.RiemannAristotlePoleQuotientOffOrdinateBudgetTargetExact as Off
import DASHI.Analysis.RiemannAristotlePoleQuotientGammaBudgetTargetExact as Gamma

------------------------------------------------------------------------
-- PRODUCER-FACING FINAL ALLOWANCE TARGETS
--
-- A bare local budget theorem is not enough for the final RH consumer.  Before
-- the independent Off/Gamma scalar carriers are welded to the final common
-- carrier, the strongest honest producer contract is:
--
--   actual local budget <= consumer-assigned allowance
--
-- in that producer's own order.  The allowance value itself is data supplied by
-- the downstream consumer/attachment, not chosen by the analytic proof.
------------------------------------------------------------------------

record PoleQuotientOffAllowancePayment : Set₁ where
  field
    target : Off.PoleQuotientOffOrdinateBudgetTarget
    assignedOffAllowance : Off.Scalar target

    offBudgetBelowAssignedAllowance :
      Off._≤_ target
        (Off.OffOrdinateBudget target (Off.universalPoleQuotientTaper target))
        assignedOffAllowance

    crossingCutoffFeedsThisExactOffProducer : Set
    crossingCutoffFeedsThisExactOffProducerReceipt :
      crossingCutoffFeedsThisExactOffProducer

    sameLiteralPoleQuotientTaperAsFinalConsumer : Set
    sameLiteralPoleQuotientTaperAsFinalConsumerReceipt :
      sameLiteralPoleQuotientTaperAsFinalConsumer

    producerReference : String

open PoleQuotientOffAllowancePayment public

record PoleQuotientGammaAllowancePayment : Set₁ where
  field
    target : Gamma.PoleQuotientGammaBudgetTarget
    assignedGammaAllowance : Gamma.Scalar target

    gammaBudgetBelowAssignedAllowance :
      Gamma._≤_ target
        (Gamma.GammaBudget target (Gamma.universalPoleQuotientTaper target))
        assignedGammaAllowance

    sameLiteralPoleQuotientTaperAsFinalConsumer : Set
    sameLiteralPoleQuotientTaperAsFinalConsumerReceipt :
      sameLiteralPoleQuotientTaperAsFinalConsumer

    producerReference : String

open PoleQuotientGammaAllowancePayment public

------------------------------------------------------------------------
-- Boundary.
------------------------------------------------------------------------

record ProducerAllowanceTargetBoundary : Set where
  constructor producer-allowance-target-boundary
  field
    bareLocalUpperBoundIsFinalConsumerPayment : Bool
    bareLocalUpperBoundIsFinalConsumerPaymentIsFalse :
      bareLocalUpperBoundIsFinalConsumerPayment ≡ false

    producerChoosesItsOwnAllowance : Bool
    producerChoosesItsOwnAllowanceIsFalse :
      producerChoosesItsOwnAllowance ≡ false

    offLeafIsBudgetBelowAssignedAllowance : Bool
    offLeafIsBudgetBelowAssignedAllowanceIsTrue :
      offLeafIsBudgetBelowAssignedAllowance ≡ true

    gammaLeafIsBudgetBelowAssignedAllowance : Bool
    gammaLeafIsBudgetBelowAssignedAllowanceIsTrue :
      gammaLeafIsBudgetBelowAssignedAllowance ≡ true

    finalAllowanceSumComparisonOccursAfterSameObjectTransport : Bool
    finalAllowanceSumComparisonOccursAfterSameObjectTransportIsTrue :
      finalAllowanceSumComparisonOccursAfterSameObjectTransport ≡ true

    rhDerived : Bool
    rhDerivedIsFalse : rhDerived ≡ false

canonicalProducerAllowanceTargetBoundary : ProducerAllowanceTargetBoundary
canonicalProducerAllowanceTargetBoundary =
  producer-allowance-target-boundary
    false refl
    false refl
    true refl
    true refl
    true refl
    false refl
