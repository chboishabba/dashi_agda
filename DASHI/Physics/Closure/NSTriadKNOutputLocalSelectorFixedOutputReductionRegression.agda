module DASHI.Physics.Closure.NSTriadKNOutputLocalSelectorFixedOutputReductionRegression where

open import Agda.Builtin.Bool using (true; false)
open import Agda.Builtin.Equality using (_≡_)

import DASHI.Physics.Closure.NSTriadKNOutputLocalSelectorFixedOutputReductionExact as Cut

-- RED surface: an output-local 0/1 selector must disappear on an active
-- fixed-output fibre, vanish on an inactive fibre, and the exact-shell collar
-- must be a specialization of that generic theorem.  None of these facts is a
-- quantitative commutator payment.

genericActiveReductionClosed :
  Cut.outputLocalActiveFixedOutputReductionClosed ≡ true
genericActiveReductionClosed =
  Cut.outputLocalActiveFixedOutputReductionClosedIsTrue

genericInactiveReductionClosed :
  Cut.outputLocalInactiveFixedOutputReductionClosed ≡ true
genericInactiveReductionClosed =
  Cut.outputLocalInactiveFixedOutputReductionClosedIsTrue

collarReductionClosed :
  Cut.collarFixedOutputSelectorReductionClosed ≡ true
collarReductionClosed =
  Cut.collarFixedOutputSelectorReductionClosedIsTrue

quantitativePaymentStillOpen :
  Cut.collarQuantitativeFixedOutputPaymentClosed ≡ false
quantitativePaymentStillOpen =
  Cut.collarQuantitativeFixedOutputPaymentClosedIsFalse
