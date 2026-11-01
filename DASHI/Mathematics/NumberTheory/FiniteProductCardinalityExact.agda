module DASHI.Mathematics.NumberTheory.FiniteProductCardinalityExact where

------------------------------------------------------------------------
-- CARDINALITY OF THE UNIQUE FINITE PRODUCT ENUMERATOR
--
-- Completeness and duplicate-freedom of `uniqueFinVectorPower` already live in
-- FiniteProductEnumerationExact.  This owner attaches the matching exact
-- cardinality to that same list:
--
--   #(Fin bound)^dimension = bound^dimension.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)
open import Data.Fin.Base using (Fin)
open import Data.List.Base using (map; cartesianProductWith; allFin)
import Data.Nat.Properties as NatP
import Data.Vec.Base as Vec
open import Relation.Binary.PropositionalEquality using (cong; trans)

import DASHI.Moonshine.ClassicalHeckeWeightKSmallWordExact as Hecke
import DASHI.Mathematics.NumberTheory.FiniteDependentPairCardinalityExact as Card
import DASHI.Mathematics.NumberTheory.FiniteProductEnumerationExact as Product
import DASHI.Mathematics.NumberTheory.FiniteWeightedReindexExact as Reindex

------------------------------------------------------------------------
-- Stdlib allFin has exactly n entries.

stdlibAllFinLength :
  (n : Nat) → Reindex.listLength (allFin n) ≡ n
stdlibAllFinLength zero = refl
stdlibAllFinLength (suc n) =
  cong suc (stdlibAllFinLength n)

------------------------------------------------------------------------
-- Cartesian-product-with cardinality.  Multiplication is oriented so the
-- recursive first-list coordinate is the second multiplicative argument.

cartesianProductWithLength :
  ∀ {A B C : Set}
    (f : A → B → C)
    (xs : List A) (ys : List B) →
  Reindex.listLength (cartesianProductWith f xs ys)
  ≡ Reindex.listLength ys * Reindex.listLength xs
cartesianProductWithLength f [] ys = refl
cartesianProductWithLength f (x ∷ xs) ys =
  trans
    (Card.appendLength
      (map (f x) ys)
      (cartesianProductWith f xs ys))
    (trans
      (cong₂ _+_
        (Card.mapLength (f x) ys)
        (cartesianProductWithLength f xs ys))
      refl)
  where
  cong₂ : ∀ {X Y Z : Set} (g : X → Y → Z)
    {a a' : X} {b b' : Y} →
    a ≡ a' → b ≡ b' → g a b ≡ g a' b'
  cong₂ g refl refl = refl

------------------------------------------------------------------------
-- Exact size of the canonical unique Fin-vector power.

uniqueFinVectorPowerLength :
  (bound dimension : Nat) →
  Reindex.listLength (Product.uniqueFinVectorPower bound dimension)
  ≡ Hecke.powNat bound dimension
uniqueFinVectorPowerLength bound zero = refl
uniqueFinVectorPowerLength bound (suc dimension) =
  trans
    (cartesianProductWithLength
      Vec._∷_
      (allFin bound)
      (Product.uniqueFinVectorPower bound dimension))
    (trans
      (cong₂ _*_
        (uniqueFinVectorPowerLength bound dimension)
        (stdlibAllFinLength bound))
      (NatP.*-comm (Hecke.powNat bound dimension) bound))
  where
  cong₂ : ∀ {X Y Z : Set} (g : X → Y → Z)
    {a a' : X} {b b' : Y} →
    a ≡ a' → b ≡ b' → g a b ≡ g a' b'
  cong₂ g refl refl = refl

------------------------------------------------------------------------
-- Pure finite cardinality; no partition or analytic semantics occur here.
------------------------------------------------------------------------
