module DASHI.Core.GeneralResidualFibreCardinalityExact where

open import DASHI.Core.Prelude
open import Data.Fin.Base using (Fin)
open import Data.Fin.Properties using (_≟_)
open import Relation.Nullary.Decidable.Core using (yes; no)

import DASHI.Core.ResidualFibreLowerBoundExact as Lower

------------------------------------------------------------------------
-- ARBITRARY-k RESIDUAL CARDINALITY LOWER BOUND
--
-- Cardinality is expressed constructively: if a coarse fibre contains k
-- pairwise future-distinct representatives, every dynamically sufficient
-- residual receives an injection Fin k -> Residual.  This is exactly the
-- information-theoretic content |Residual| >= k without assuming a global
-- finite-cardinality library for arbitrary residual carriers.
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
    equalOrContradiction i j equality with i ≟ j
    ... | yes indicesEqual = indicesEqual
    ... | no indicesDifferent =
      ⊥-elim
        (pairwiseFutureDistinct fibre indicesDifferent
          (Lower.pairKernelFutureSafe safe
            (trans (inSameFibre fibre i) (sym (inSameFibre fibre j)))
            equality))

------------------------------------------------------------------------
-- Fixed-bit reduction.  A b-bit residual carrier has 2^b words.  The theorem
-- below deliberately reduces the bit lower bound to the finite pigeonhole
-- statement `NoInjection (Fin k) (Fin (2^b))`; it does not hide that separate
-- combinatorial obligation behind a numerical slogan.
------------------------------------------------------------------------

pow2 : Nat → Nat
pow2 zero = 1
pow2 (suc bits) = 2 * pow2 bits

BitWords : Nat → Set
BitWords bits = Fin (pow2 bits)

NoInjection : ∀ {A B : Set} → Set
NoInjection {A} {B} = (f : A → B) → Injective f → ⊥

bitBudgetTooSmallContradictsFutureSafety :
  ∀ {State Coarse k bits}
    {FutureEq : State → State → Set}
    {coarsen : State → Coarse}
    {residual : State → BitWords bits}
    (safe : Lower.DynamicallySufficientPair
      State Coarse (BitWords bits) FutureEq coarsen residual)
    (fibre : FiniteFutureDistinctFibre k FutureEq coarsen) →
  NoInjection {Fin k} {BitWords bits} → ⊥
bitBudgetTooSmallContradictsFutureSafety safe fibre noInjection =
  noInjection
    (λ index → residual (representative fibre index))
    (residualInjectionFromFutureDistinctFibre safe fibre)

------------------------------------------------------------------------
-- This is the general theorem surface behind b >= ceil(log2 k): once the
-- arithmetic library proves k > 2^b implies no injection Fin k -> Fin (2^b),
-- the bit bound follows immediately through the theorem above.
------------------------------------------------------------------------
