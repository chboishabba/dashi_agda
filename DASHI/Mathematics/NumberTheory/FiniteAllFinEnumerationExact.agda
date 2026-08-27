module DASHI.Mathematics.NumberTheory.FiniteAllFinEnumerationExact where

------------------------------------------------------------------------
-- CANONICAL FIN ENUMERATION RECEIPTS
--
-- Keep completeness, uniqueness and cardinality attached to the same explicit
-- allFin list used by FiniteProductEnumerationExact.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Empty using (⊥)
open import Data.Fin.Base using (Fin)
  renaming (zero to fzero; suc to fsuc)
open import Data.List.Base using (map)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Membership.Propositional.Properties using (∈-map⁻)
import Data.List.Relation.Unary.All as All
import Data.List.Relation.Unary.AllPairs.Core as AllPairs
open import Data.List.Relation.Unary.Unique.Propositional using (Unique)
import Data.List.Relation.Unary.Unique.Propositional.Properties as UniqueP
open import Data.Product using (Σ; _,_)
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)

import DASHI.Mathematics.NumberTheory.FiniteProductEnumerationExact as Product
import DASHI.Mathematics.NumberTheory.FiniteWeightedReindexExact as Reindex

allFin : (n : Nat) → List (Fin n)
allFin = Product.allFin

allFinComplete : ∀ {n} (index : Fin n) → index ∈ allFin n
allFinComplete = Product.allFinComplete

mapLength :
  ∀ {A B : Set} (f : A → B) (xs : List A) →
  Reindex.listLength (map f xs) ≡ Reindex.listLength xs
mapLength f [] = refl
mapLength f (_ ∷ xs) = cong suc (mapLength f xs)

allFinLength : (n : Nat) → Reindex.listLength (allFin n) ≡ n
allFinLength zero = refl
allFinLength (suc n) =
  cong suc
    (trans
      (mapLength fsuc (allFin n))
      (allFinLength n))

fzeroNotSuccessor : ∀ {n} {index : Fin n} → fzero ≡ fsuc index → ⊥
fzeroNotSuccessor ()

fzeroNotInMappedSuccessors :
  ∀ {n} → All.All (λ index → fzero ≡ index → ⊥)
    (map fsuc (allFin n))
fzeroNotInMappedSuccessors =
  All.tabulate λ member equality →
    helper (∈-map⁻ fsuc member) equality
  where
  helper :
    ∀ {n} {target : Fin (suc n)} →
    Σ (Fin n) (λ source → source ∈ allFin n × target ≡ fsuc source) →
    fzero ≡ target → ⊥
  helper (source , sourceMember , targetIsSuccessor) zeroIsTarget =
    fzeroNotSuccessor (trans zeroIsTarget targetIsSuccessor)

allFinUnique : (n : Nat) → Unique (allFin n)
allFinUnique zero = AllPairs.[]
allFinUnique (suc n) =
  AllPairs._∷_
    fzeroNotInMappedSuccessors
    (UniqueP.map⁺ fsucInjective (allFinUnique n))
  where
  fsucInjective : ∀ {left right : Fin n} → fsuc left ≡ fsuc right → left ≡ right
  fsucInjective refl = refl

------------------------------------------------------------------------
-- Pure finite enumeration.
------------------------------------------------------------------------
