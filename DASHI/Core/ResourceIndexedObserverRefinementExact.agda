module DASHI.Core.ResourceIndexedObserverRefinementExact where

------------------------------------------------------------------------
-- RESOURCE-INDEXED OBSERVER REFINEMENT
--
-- Structural refinement and operational affordability are distinct.
--
-- A fine observer may strictly separate a collision that a coarse observer
-- merges while still exceeding a declared resource/access budget.
--
-- "Cost" is intentionally uninterpreted here: domains may instantiate it as
-- runtime, evidence-access cost, privacy cost, bandwidth, storage, money, or
-- another explicit resource coordinate.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.Unit using (⊤; tt)
open import Data.Empty using (⊥)
open import Data.Nat.Base using (_≤_; z≤n; s≤s)

import DASHI.Core.ObserverRefinementLatticeExact as Observer

WithinBudget : Nat → Nat → Set
WithinBudget budget cost = cost ≤ budget

record CostedStrictRefinement
    {State Coarse Fine : Set}
    (coarse : State → Coarse)
    (fine : State → Fine) : Set₁ where
  constructor costed-strict-refinement
  field
    strict : Observer.StrictRefinement coarse fine
    coarseCost : Nat
    fineCost : Nat

open CostedStrictRefinement public

record BudgetAdmissibleStrictRefinement
    {State Coarse Fine : Set}
    (coarse : State → Coarse)
    (fine : State → Fine) : Set₁ where
  constructor budget-admissible-strict-refinement
  field
    costed : CostedStrictRefinement coarse fine
    budget : Nat
    coarseWithinBudget : WithinBudget budget (coarseCost costed)
    fineWithinBudget : WithinBudget budget (fineCost costed)

open BudgetAdmissibleStrictRefinement public

budgetAdmissibleImpliesStrict :
  ∀ {State Coarse Fine}
    {coarse : State → Coarse}
    {fine : State → Fine} →
  BudgetAdmissibleStrictRefinement coarse fine →
  Observer.StrictRefinement coarse fine
budgetAdmissibleImpliesStrict receipt =
  strict (costed receipt)

record RefinementBudgetFailure
    {State Coarse Fine : Set}
    (coarse : State → Coarse)
    (fine : State → Fine) : Set₁ where
  constructor refinement-budget-failure
  field
    strictRefinement : Observer.StrictRefinement coarse fine
    budget : Nat
    coarseCost fineCost : Nat
    coarseAffordable : WithinBudget budget coarseCost
    fineUnaffordable : WithinBudget budget fineCost → ⊥

open RefinementBudgetFailure public

------------------------------------------------------------------------
-- Exact finite witness.
------------------------------------------------------------------------

data DemoState : Set where
  demoLeft : DemoState
  demoRight : DemoState

demoCoarse : DemoState → ⊤
demoCoarse _ = tt

demoFine : DemoState → Bool
demoFine demoLeft = false
demoFine demoRight = true

demoFineSeparates :
  demoFine demoLeft ≡ demoFine demoRight → ⊥
demoFineSeparates ()

demoStrictRefinement :
  Observer.StrictRefinement demoCoarse demoFine
demoStrictRefinement =
  Observer.strictRefinement
    (λ x y sameFine → refl)
    demoLeft
    demoRight
    refl
    demoFineSeparates

oneWithinOne : WithinBudget 1 1
oneWithinOne = s≤s z≤n

twoNotWithinOne : WithinBudget 1 2 → ⊥
twoNotWithinOne ()

canonicalRefinementBudgetFailure :
  RefinementBudgetFailure demoCoarse demoFine
canonicalRefinementBudgetFailure =
  refinement-budget-failure
    demoStrictRefinement
    1
    1
    2
    oneWithinOne
    twoNotWithinOne

------------------------------------------------------------------------
-- Non-promotion boundary.
------------------------------------------------------------------------

record ResourceIndexedObserverBoundary : Set where
  constructor resource-indexed-observer-boundary
  field
    strictRefinementImpliesBudgetAdmissible : Bool
    affordableCoarseImpliesAffordableFine : Bool
    structuralAndResourceAxesRemainSeparate : Bool

canonicalResourceIndexedObserverBoundary :
  ResourceIndexedObserverBoundary
canonicalResourceIndexedObserverBoundary =
  resource-indexed-observer-boundary
    false false true
