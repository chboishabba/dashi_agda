module DASHI.Physics.Closure.NSTriadKNCollarHeatNestedSameOutputWeldRegression where

open import Agda.Builtin.Bool using (true; false)
open import Agda.Builtin.Equality using (_≡_)

import DASHI.Physics.Closure.NSTriadKNCollarHeatNestedSameOutputWeldExact as Weld

collarUsesSameR98OuterCarrierIsTrue :
  Weld.collarUsesSameR98OuterCarrier ≡ true
collarUsesSameR98OuterCarrierIsTrue = Weld.collarUsesSameR98OuterCarrierIsTrue

sameOutputPreservesCollarSelectorIsTrue :
  Weld.sameOutputPreservesCollarSelector ≡ true
sameOutputPreservesCollarSelectorIsTrue =
  Weld.sameOutputPreservesCollarSelectorIsTrue

collarQuantitativeSignedBudgetClosedIsFalse :
  Weld.collarQuantitativeSignedBudgetClosed ≡ false
collarQuantitativeSignedBudgetClosedIsFalse =
  Weld.collarQuantitativeSignedBudgetClosedIsFalse
