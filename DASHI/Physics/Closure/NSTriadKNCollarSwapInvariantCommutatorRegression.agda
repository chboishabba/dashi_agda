module DASHI.Physics.Closure.NSTriadKNCollarSwapInvariantCommutatorRegression where

open import Agda.Builtin.Bool using (true; false)
open import Agda.Builtin.Equality using (_≡_)

import DASHI.Physics.Closure.NSTriadKNCollarSwapInvariantCommutatorExact as Collar

collarWeightSwapInvariantClosedIsTrue :
  Collar.collarWeightSwapInvariantClosed ≡ true
collarWeightSwapInvariantClosedIsTrue =
  Collar.collarWeightSwapInvariantClosedIsTrue

collarFixedOutputCommutatorCollapseClosedIsTrue :
  Collar.collarFixedOutputCommutatorCollapseClosed ≡ true
collarFixedOutputCommutatorCollapseClosedIsTrue =
  Collar.collarFixedOutputCommutatorCollapseClosedIsTrue

collarQuantitativeFixedOutputPaymentClosedIsFalse :
  Collar.collarQuantitativeFixedOutputPaymentClosed ≡ false
collarQuantitativeFixedOutputPaymentClosedIsFalse =
  Collar.collarQuantitativeFixedOutputPaymentClosedIsFalse
