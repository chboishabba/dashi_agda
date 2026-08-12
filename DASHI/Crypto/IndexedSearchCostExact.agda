module DASHI.Crypto.IndexedSearchCostExact where

------------------------------------------------------------------------
-- INDEXED SEARCH / RECONCILIATION COST ACCOUNTING
--
-- The verifier-to-search seam is only additive when reconciliation is itself
-- constructive/functional.  Generic survivor sets pay a Cartesian product.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; _+_; _*_)

sumNat : List Nat → Nat
sumNat [] = zero
sumNat (x ∷ xs) = x + sumNat xs

productNat : List Nat → Nat
productNat [] = 1
productNat (x ∷ xs) = x * productNat xs

indexedCartesianSearchCost :
  List Nat → List Nat → Nat → Nat
indexedCartesianSearchCost localCosts survivorCounts reconcilePerTuple =
  sumNat localCosts + productNat survivorCounts * reconcilePerTuple

indexedFunctionalSearchCost :
  List Nat → Nat → Nat
indexedFunctionalSearchCost localCosts reconciliationCost =
  sumNat localCosts + reconciliationCost

record CartesianSearchAccounting : Set where
  constructor cartesianSearchAccounting
  field
    localCosts survivorCounts : List Nat
    reconcilePerTuple : Nat
    total : Nat
    totalExact :
      total ≡ indexedCartesianSearchCost
        localCosts survivorCounts reconcilePerTuple

open CartesianSearchAccounting public

record FunctionalSearchAccounting : Set where
  constructor functionalSearchAccounting
  field
    localCosts : List Nat
    reconciliationCost : Nat
    total : Nat
    totalExact :
      total ≡ indexedFunctionalSearchCost localCosts reconciliationCost

open FunctionalSearchAccounting public

------------------------------------------------------------------------
-- Concrete regression: two local enumerators with 3 and 5 surviving states.
------------------------------------------------------------------------

twoLaneLocalCosts : List Nat
twoLaneLocalCosts = 7 ∷ 11 ∷ []

twoLaneSurvivors : List Nat
twoLaneSurvivors = 3 ∷ 5 ∷ []

twoLaneCartesianCost :
  indexedCartesianSearchCost twoLaneLocalCosts twoLaneSurvivors 2 ≡ 48
twoLaneCartesianCost = refl

twoLaneFunctionalCost :
  indexedFunctionalSearchCost twoLaneLocalCosts 2 ≡ 20
twoLaneFunctionalCost = refl

record ReconciliationMode : Set where
  constructor reconciliationMode
  field
    survivorProductCharged : Nat
    reconciliationWork : Nat
    totalWork : Nat

open ReconciliationMode public

cartesianMode : ReconciliationMode
cartesianMode = reconciliationMode 15 30 48

functionalMode : ReconciliationMode
functionalMode = reconciliationMode 1 2 20

------------------------------------------------------------------------
-- The formulas themselves are exact accounting, not complexity claims about a
-- concrete primitive until its local enumerators and reconciliation algorithm
-- instantiate the costs.
------------------------------------------------------------------------
