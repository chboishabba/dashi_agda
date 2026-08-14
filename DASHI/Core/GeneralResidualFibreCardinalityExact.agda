module DASHI.Core.GeneralResidualFibreCardinalityExact where

open import DASHI.Core.Prelude
open import Data.Fin.Base using (Fin)
import Data.Fin.Properties as Finₚ
open import Relation.Nullary.Decidable.Core using (yes; no)

import DASHI.Core.ResidualFibreLowerBoundExact as Lower

------------------------------------------------------------------------
-- ARBITRARY-k RESIDUAL CARDINALITY LOWER BOUND
------------------------------------------------------------------------

Injective : ∀ {A B : Set} → (A → B) → Set
Injective f = ∀ {left right} → f left ≡ f right → left ≡ right

record FiniteFutureDistinctFibre
    {State Coarse : Set}
    (k : Nat)
    (FutureEq : State → State → Set)
    (coarsen : State → Coarse) : Set₁ where
  constructor finiteFutureDistinctFibre
  field
    representative : Fin k → State
    fibreClass : Coarse
    inSameFibre : (index : Fin k) → coarsen (representative index) ≡ fibreClass
    pairwiseFutureDistinct :
      ∀ {left right} →
      (left ≡ right → ⊥) →
      FutureEq (representative left) (representative right) → ⊥

open FiniteFutureDistinctFibre public

residualInjectionFromFutureDistinctFibre :
  ∀ {State Coarse Residual k}
    {FutureEq : State → State → Set}
    {coarsen : State → Coarse}
    {residual : State → Residual}
    (safe : Lower.DynamicallySufficientPair
      State Coarse Residual FutureEq coarsen residual)
    (fibre : FiniteFutureDistinctFibre k FutureEq coarsen) →
  Injective (λ index → residual (representative fibre index))
residualInjectionFromFutureDistinctFibre safe fibre {left} {right} residualEqual =
  equalOrContradiction left right residualEqual
  where
    equalOrContradiction :
      (i j : Fin k) →
      residual (representative fibre i) ≡ residual (representative fibre j) →
      i ≡ j
    equalOrContradiction i j equality with Finₚ._≟_ i j
    ... | yes indicesEqual = indicesEqual
    ... | no indicesDifferent =
      ⊥-elim
        (pairwiseFutureDistinct fibre indicesDifferent
          (Lower.pairKernelFutureSafe safe
            (trans (inSameFibre fibre i) (sym (inSameFibre fibre j)))
            equality))

------------------------------------------------------------------------
-- Fixed-bit consequence.  A b-bit carrier has 2^b codewords.  Data.Fin's
-- constructive pigeonhole theorem turns the residual injection into the exact
-- numerical capacity inequality k <= 2^b.
------------------------------------------------------------------------

pow2 : Nat → Nat
pow2 zero = 1
pow2 (suc bits) = 2 * pow2 bits

BitWords : Nat → Set
BitWords bits = Fin (pow2 bits)

futureSafetyForBitWordsImpliesCapacityBound :
  ∀ {State Coarse k bits}
    {FutureEq : State → State → Set}
    {coarsen : State → Coarse}
    {residual : State → BitWords bits}
    (safe : Lower.DynamicallySufficientPair
      State Coarse (BitWords bits) FutureEq coarsen residual)
    (fibre : FiniteFutureDistinctFibre k FutureEq coarsen) →
  k ≤ pow2 bits
futureSafetyForBitWordsImpliesCapacityBound safe fibre =
  Finₚ.injective⇒≤
    (residualInjectionFromFutureDistinctFibre safe fibre)

bitBudgetBelowClassCountIsImpossible :
  ∀ {State Coarse k bits}
    {FutureEq : State → State → Set}
    {coarsen : State → Coarse}
    {residual : State → BitWords bits}
    (safe : Lower.DynamicallySufficientPair
      State Coarse (BitWords bits) FutureEq coarsen residual)
    (fibre : FiniteFutureDistinctFibre k FutureEq coarsen) →
  pow2 bits < k → ⊥
bitBudgetBelowClassCountIsImpossible safe fibre tooSmall =
  ≤⇒≯ (futureSafetyForBitWordsImpliesCapacityBound safe fibre) tooSmall

------------------------------------------------------------------------
-- Thus every safe fixed-bit residual obeys k <= 2^b, equivalently
-- b >= ceil(log2 k) once ceil-log2 is chosen as the least b with k <= 2^b.
------------------------------------------------------------------------
