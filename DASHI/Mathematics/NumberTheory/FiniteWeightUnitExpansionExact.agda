module DASHI.Mathematics.NumberTheory.FiniteWeightUnitExpansionExact where

------------------------------------------------------------------------
-- DASHI CONTRIBUTION
--
-- Expand a finite natural-valued weight into an explicit finite fibre.
-- An item of weight w is replaced by w unit-labelled copies indexed by Fin w.
-- Therefore a weighted fold is literally the cardinality / unit-mass fold of
-- a concrete expanded enumeration.
--
-- This is the generic theorem needed on the right side of Erdos's identity:
-- the coefficient v in
--
--   sum_v sum_k v p(n-kv)
--
-- becomes an actual Fin v fibre rather than a numerical annotation.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; _+_)
open import Data.Fin.Base using (Fin)
open import Data.List.Base using (map; _++_)
open import Data.Product using (Σ; _,_)
open import Relation.Binary.PropositionalEquality using (cong; trans)

import DASHI.Mathematics.NumberTheory.FiniteWeightedReindexExact as Reindex
import DASHI.Mathematics.NumberTheory.PartitionMarkedUnitEnumerationExact as Finite

------------------------------------------------------------------------
-- Dependent unit-labelled expansion.

UnitExpansion : ∀ {A : Set} → (A → Nat) → Set
UnitExpansion {A} weight = Σ A (λ item → Fin (weight item))

expandOne :
  ∀ {A : Set} (weight : A → Nat) →
  (item : A) → List (UnitExpansion weight)
expandOne weight item =
  map (λ index → item , index) (Finite.allFin (weight item))

expandOneLength :
  ∀ {A : Set} (weight : A → Nat) →
  (item : A) →
  Reindex.listLength (expandOne weight item) ≡ weight item
expandOneLength weight item =
  trans
    (Finite.mapLength
      (λ index → item , index)
      (Finite.allFin (weight item)))
    (Finite.allFinLength (weight item))

expandEnumeration :
  ∀ {A : Set} (weight : A → Nat) →
  List A → List (UnitExpansion weight)
expandEnumeration weight [] = []
expandEnumeration weight (item ∷ items) =
  expandOne weight item ++ expandEnumeration weight items

expandEnumerationLength :
  ∀ {A : Set} (weight : A → Nat) →
  (items : List A) →
  Reindex.listLength (expandEnumeration weight items)
  ≡ Reindex.foldNat weight items
expandEnumerationLength weight [] = refl
expandEnumerationLength weight (item ∷ items) =
  trans
    (Finite.appendLength
      (expandOne weight item)
      (expandEnumeration weight items))
    (cong₂ _+_
      (expandOneLength weight item)
      (expandEnumerationLength weight items))
  where
    cong₂ : ∀ {A B C : Set} (f : A → B → C)
      {x x' : A} {y y' : B} →
      x ≡ x' → y ≡ y' → f x y ≡ f x' y'
    cong₂ f refl refl = refl

unitWeight :
  ∀ {A : Set} {weight : A → Nat} →
  UnitExpansion weight → Nat
unitWeight _ = 1

expandedUnitFold :
  ∀ {A : Set} (weight : A → Nat) →
  List A → Nat
expandedUnitFold weight items =
  Reindex.foldNat unitWeight (expandEnumeration weight items)

expandedUnitFoldEqualsWeightedFold :
  ∀ {A : Set} (weight : A → Nat) →
  (items : List A) →
  expandedUnitFold weight items ≡ Reindex.foldNat weight items
expandedUnitFoldEqualsWeightedFold weight items =
  trans
    (Reindex.foldOneIsLength (expandEnumeration weight items))
    (expandEnumerationLength weight items)

------------------------------------------------------------------------
-- The theorem is purely finite.  No semiring quotient, cardinal arithmetic,
-- convergence argument, or proof irrelevance is used.
------------------------------------------------------------------------
