module DASHI.Mathematics.NumberTheory.FiniteAllFinEnumerationExact where

------------------------------------------------------------------------
-- CANONICAL FIN ENUMERATION RECEIPTS
--
-- Keep completeness, uniqueness and cardinality attached to the same explicit
-- allFin list used by FiniteProductEnumerationExact.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Fin.Base using (Fin)
  renaming (zero to fzero; suc to fsuc)
open import Data.List.Base using (map)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Membership.Propositional.Properties using (∈-map⁻)
open import Data.List.Relation.Unary.Any as Any using ()
import Data.List.Relation.Unary.All as All
import Data.List.Relation.Unary.AllPairs.Core as AllPairs
open import Data.List.Relation.Unary.Unique.Propositional using (Unique)
import Data.List.Relation.Unary.Unique.Propositional.Properties as UniqueP
open import Data.Product using (Σ; _,_)
open import Relation.Binary.PropositionalEquality using (cong)

import DASHI.Mathematics.NumberTheory.FiniteProductEnumerationExact as Product
import DASHI.Mathematics.NumberTheory.FiniteWeightedReindexExact as Reindex

allFin : (n : Nat) → Data.List.Base.List (Fin n)
allFin = Product.allFin

allFinComplete : ∀ {n} (index : Fin n) → index ∈ allFin n
allFinComplete = Product.allFinComplete

mapLength :
  ∀ {A B : Set} (f : A → B) (xs : Data.List.Base.List A) →
  Reindex.listLength (map f xs) ≡ Reindex.listLength xs
mapLength f Data.List.Base.[] = refl
mapLength f (_ Data.List.Base.∷ xs) = cong suc (mapLength f xs)

allFinLength : (n : Nat) → Reindex.listLength (allFin n) ≡ n
allFinLength zero = refl
allFinLength (suc n) =
  cong suc
    (Data.Relation.Binary.PropositionalEquality.Core.trans
      (mapLength fsuc (allFin n))
      (allFinLength n))

fzeroNotInMappedSuccessors :
  ∀ {n} → All.All (λ index → fzero ≡ index → Data.Empty.⊥)
    (map fsuc (allFin n))
fzeroNotInMappedSuccessors =
  All.tabulate λ member equality →
    let witness = ∈-map⁻ fsuc member
    in helper witness equality
  where
  helper :
    ∀ {n} →
    Σ (Fin n) (λ source → source ∈ allFin n × fsuc source ≡ fzero) →
    fzero ≡ fzero → Data.Empty.⊥
  helper (source , sourceMember , ()) equality

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
