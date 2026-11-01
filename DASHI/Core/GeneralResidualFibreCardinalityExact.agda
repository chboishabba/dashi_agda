module DASHI.Core.GeneralResidualFibreCardinalityExact where

open import DASHI.Core.Prelude
open import Data.Fin.Base using (Fin)
import Data.Fin.Properties as Finₚ

import DASHI.Core.ResidualFibreLowerBoundExact as Lower

Injective : ∀ {A B : Set} → (A → B) → Set
Injective f = ∀ {left right} → f left ≡ f right → left ≡ right

------------------------------------------------------------------------
-- A finite future-distinct fibre is enumerated by Fin k.  The strongest clean
-- formulation of pairwise future distinction is extensional: if two enumerated
-- representatives are future-equivalent, their indices were already equal.
------------------------------------------------------------------------

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
    futureEquivalentIndicesEqual :
      ∀ {left right} →
      FutureEq (representative left) (representative right) →
      left ≡ right

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
  futureEquivalentIndicesEqual fibre
    (Lower.pairKernelFutureSafe safe
      (trans (inSameFibre fibre left) (sym (inSameFibre fibre right)))
      residualEqual)

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

record CeilLog2Certificate (k bits : Nat) : Set where
  constructor ceilLog2Certificate
  field
    hasCapacity : k ≤ pow2 bits
    leastCapacity :
      (candidateBits : Nat) →
      k ≤ pow2 candidateBits →
      bits ≤ candidateBits

open CeilLog2Certificate public

safeBitResidualRespectsCeilLog2 :
  ∀ {State Coarse k bits minimumBits}
    {FutureEq : State → State → Set}
    {coarsen : State → Coarse}
    {residual : State → BitWords bits}
    (ceilCertificate : CeilLog2Certificate k minimumBits)
    (safe : Lower.DynamicallySufficientPair
      State Coarse (BitWords bits) FutureEq coarsen residual)
    (fibre : FiniteFutureDistinctFibre k FutureEq coarsen) →
  minimumBits ≤ bits
safeBitResidualRespectsCeilLog2 ceilCertificate safe fibre =
  leastCapacity ceilCertificate bits
    (futureSafetyForBitWordsImpliesCapacityBound safe fibre)

------------------------------------------------------------------------
-- Every future-safe fixed-bit residual therefore obeys k <= 2^b and any
-- certified least-capacity exponent gives b >= ceil(log2 k).
------------------------------------------------------------------------
