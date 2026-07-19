module DASHI.Core.QuantitativeNonlinearSparsity where

open import DASHI.Core.Prelude
open import DASHI.Core.NonlinearExplodedSparsity
open import Relation.Nullary using (Dec)

------------------------------------------------------------------------
-- Abstract finite counting interface
------------------------------------------------------------------------

record FiniteCounting (X : Set) : Set₁ where
  field
    count : (X → Set) → Nat
    monotone : {P Q : X → Set} →
      ((x : X) → P x → Q x) → count P ≤ count Q

open FiniteCounting public

record SparseAtMost
  {X : Set}
  (C : FiniteCounting X)
  (P : X → Set)
  (budget : Nat) : Set where
  field
    bounded : count C P ≤ budget

open SparseAtMost public

------------------------------------------------------------------------
-- Quantitative nonlinear sparsity theorem
------------------------------------------------------------------------

defectCount≤lowMarginCount :
  {X L : Set} {K : ThresholdKernel X L} {s : State X}
  {LowMargin : X → Set} →
  (C : FiniteCounting X) →
  MarginControl K s LowMargin →
  ((x : X) → Dec (LowMargin x)) →
  count C (KernelDefect K s) ≤ count C LowMargin
defectCount≤lowMarginCount C control decideLow =
  monotone C (defectConfined control decideLow)

sparseLowMarginImpliesSparseDefect :
  {X L : Set} {K : ThresholdKernel X L} {s : State X}
  {LowMargin : X → Set} {budget : Nat} →
  (C : FiniteCounting X) →
  MarginControl K s LowMargin →
  ((x : X) → Dec (LowMargin x)) →
  SparseAtMost C LowMargin budget →
  SparseAtMost C (KernelDefect K s) budget
sparseLowMarginImpliesSparseDefect C control decideLow sparse = record
  { bounded =
      ≤-trans
        (defectCount≤lowMarginCount C control decideLow)
        (bounded sparse)
  }

------------------------------------------------------------------------
-- Relative sparsity certificate
------------------------------------------------------------------------

record RelativeSparsity
  {X : Set}
  (C : FiniteCounting X)
  (P : X → Set) : Set₁ where
  field
    ambient : Nat
    budget  : Nat
    ambientCount : count C (λ _ → ⊤) ≡ ambient
    sparseBound  : count C P ≤ budget
    budgetWithinAmbient : budget ≤ ambient

open RelativeSparsity public

defectRelativeSparsity :
  {X L : Set} {K : ThresholdKernel X L} {s : State X}
  {LowMargin : X → Set} →
  (C : FiniteCounting X) →
  MarginControl K s LowMargin →
  ((x : X) → Dec (LowMargin x)) →
  RelativeSparsity C LowMargin →
  RelativeSparsity C (KernelDefect K s)
defectRelativeSparsity C control decideLow sparse = record
  { ambient = ambient sparse
  ; budget = budget sparse
  ; ambientCount = ambientCount sparse
  ; sparseBound =
      ≤-trans
        (defectCount≤lowMarginCount C control decideLow)
        (sparseBound sparse)
  ; budgetWithinAmbient = budgetWithinAmbient sparse
  }
