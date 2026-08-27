module DASHI.Mathematics.NumberTheory.FiniteDependentPairCardinalityExact where

------------------------------------------------------------------------
-- CARDINALITY OF A FINITE DEPENDENT SUM
--
-- For a finite base list xs and finite fibre lists Y(x),
--
--   # (Sigma x in xs, Y(x)) = sum_x #Y(x).
--
-- This is the counting companion to FiniteDependentPairEnumerationExact.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; _+_)
open import Data.List.Base using (map; _++_)
open import Data.Product using (Σ; _,_)
open import Relation.Binary.PropositionalEquality using (cong; trans)

import DASHI.Mathematics.NumberTheory.FiniteDependentPairEnumerationExact as Dep
import DASHI.Mathematics.NumberTheory.FiniteWeightedReindexExact as Reindex

mapLength :
  ∀ {A B : Set} (f : A → B) (xs : List A) →
  Reindex.listLength (map f xs) ≡ Reindex.listLength xs
mapLength f [] = refl
mapLength f (_ ∷ xs) = cong (1 +_) (mapLength f xs)

appendLength :
  ∀ {A : Set} (xs ys : List A) →
  Reindex.listLength (xs ++ ys)
  ≡ Reindex.listLength xs + Reindex.listLength ys
appendLength [] ys = refl
appendLength (_ ∷ xs) ys =
  cong (1 +_) (appendLength xs ys)

pairBlockLength :
  ∀ {A : Set} {B : A → Set}
    (x : A) (values : List (B x)) →
  Reindex.listLength (Dep.pairBlock x values)
  ≡ Reindex.listLength values
pairBlockLength x values = mapLength (λ value → x , value) values

dependentPairsLength :
  ∀ {A : Set} {B : A → Set}
    (xs : List A) (fibres : (x : A) → List (B x)) →
  Reindex.listLength (Dep.dependentPairs xs fibres)
  ≡ Reindex.foldNat (λ x → Reindex.listLength (fibres x)) xs
dependentPairsLength [] fibres = refl
dependentPairsLength (x ∷ xs) fibres =
  trans
    (appendLength
      (Dep.pairBlock x (fibres x))
      (Dep.dependentPairs xs fibres))
    (trans
      (cong₂ _+_
        (pairBlockLength x (fibres x))
        (dependentPairsLength xs fibres))
      refl)
  where
  cong₂ : ∀ {A B C : Set} (f : A → B → C)
    {a a' : A} {b b' : B} →
    a ≡ a' → b ≡ b' → f a b ≡ f a' b'
  cong₂ f refl refl = refl

------------------------------------------------------------------------
-- Pure finite list arithmetic; no domain semantics occur here.
------------------------------------------------------------------------
