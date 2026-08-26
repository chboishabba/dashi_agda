module DASHI.Mathematics.NumberTheory.PartitionMarkedUnitEnumerationExact where

------------------------------------------------------------------------
-- DASHI CONTRIBUTION
--
-- For any finite enumeration of objects at grade n, enumerate the marked
-- carrier obtained by pairing each object with one of n unit positions.
-- The resulting list has exactly
--
--   n * (# objects)
--
-- elements.  In the partition lane this supplies the left side n*p(n) of the
-- Erdos double count without adding a partition-specific counting axiom.
--
-- This is another finite-cardinality cross-pollination with the repo's fibre
-- machinery: a grade-n object has a canonical Fin n marking fibre.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)
open import Data.Fin.Base using (Fin; zero; suc)
open import Data.List.Base using (map; _++_)
open import Data.Product using (_×_; _,_)
open import Relation.Binary.PropositionalEquality using (cong; trans)

import DASHI.Mathematics.NumberTheory.FiniteWeightedReindexExact as Reindex

------------------------------------------------------------------------
-- Canonical enumeration of Fin n.

allFin : (n : Nat) → List (Fin n)
allFin zero = []
allFin (suc n) = zero ∷ map suc (allFin n)

mapLength :
  ∀ {A B : Set} (f : A → B) (items : List A) →
  Reindex.listLength (map f items) ≡ Reindex.listLength items
mapLength f [] = refl
mapLength f (_ ∷ xs) = cong (1 +_) (mapLength f xs)

allFinLength :
  (n : Nat) → Reindex.listLength (allFin n) ≡ n
allFinLength zero = refl
allFinLength (suc n) =
  cong (1 +_) (trans (mapLength suc (allFin n)) (allFinLength n))

------------------------------------------------------------------------
-- Pair one object with every unit position in its grade.

markOne :
  ∀ {A : Set} {n : Nat} → A → List (A × Fin n)
markOne {n = n} object = map (λ index → object , index) (allFin n)

markOneLength :
  ∀ {A : Set} {n : Nat} (object : A) →
  Reindex.listLength (markOne {n = n} object) ≡ n
markOneLength {n = n} object =
  trans
    (mapLength (λ index → object , index) (allFin n))
    (allFinLength n)

appendLength :
  ∀ {A : Set} (left right : List A) →
  Reindex.listLength (left ++ right)
  ≡ Reindex.listLength left + Reindex.listLength right
appendLength [] right = refl
appendLength (_ ∷ left) right =
  cong (1 +_) (appendLength left right)

------------------------------------------------------------------------
-- Mark every object in a finite grade enumeration.

markEnumeration :
  ∀ {A : Set} {n : Nat} → List A → List (A × Fin n)
markEnumeration [] = []
markEnumeration {n = n} (object ∷ objects) =
  markOne {n = n} object ++ markEnumeration {n = n} objects

markEnumerationLength :
  ∀ {A : Set} {n : Nat} (objects : List A) →
  Reindex.listLength (markEnumeration {n = n} objects)
  ≡ n * Reindex.listLength objects
markEnumerationLength {n = n} [] = refl
markEnumerationLength {n = n} (object ∷ objects) =
  trans
    (appendLength
      (markOne {n = n} object)
      (markEnumeration {n = n} objects))
    (trans
      (cong₂ _+_
        (markOneLength {n = n} object)
        (markEnumerationLength {n = n} objects))
      refl)
  where
    cong₂ : ∀ {A B C : Set} (f : A → B → C)
      {x x' : A} {y y' : B} →
      x ≡ x' → y ≡ y' → f x y ≡ f x' y'
    cong₂ f refl refl = refl

------------------------------------------------------------------------
-- Constant-weight fold formulation used directly by Erdos double counting.

markedUnitFold :
  ∀ {A : Set} {n : Nat} → List A → Nat
markedUnitFold {n = n} objects =
  Reindex.foldNat (λ _ → 1) (markEnumeration {n = n} objects)

markedUnitFoldIsNCount :
  ∀ {A : Set} {n : Nat} (objects : List A) →
  markedUnitFold {n = n} objects
  ≡ n * Reindex.listLength objects
markedUnitFoldIsNCount {n = n} objects =
  trans
    (Reindex.foldOneIsLength (markEnumeration {n = n} objects))
    (markEnumerationLength {n = n} objects)
