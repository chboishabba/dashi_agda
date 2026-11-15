module DASHI.Moonshine.Monster3BLinearActionProofRelevantHardeningValidation where

-- RED-first contract for the upstream Monster linear-action proof boundary.
-- The production owner must require inhabitants of every legacy Set-valued
-- linearity/invariance obligation before downstream isotypic recognition can
-- treat the literal weight-two / zeta carriers as actual linear reps.

import DASHI.Moonshine.Monster3BLinearActionProofRelevantHardeningExact as Cut

paidWeightTwoWrapperAvailable : Set
paidWeightTwoWrapperAvailable = Cut.PaidWeightTwoLinearActionBridge

paidLinearZetaWrapperAvailable : Set
paidLinearZetaWrapperAvailable = Cut.PaidLinearSingleActionProducer

upstreamLinearityTypedObligationsAreNotPayment :
  Cut.TypedLinearityObligationCreatesPaidLinearAction → ⊥
upstreamLinearityTypedObligationsAreNotPayment =
  Cut.typedLinearityObligationDoesNotPayLinearAction
