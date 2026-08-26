module DASHI.Mathematics.NumberTheory.FiniteWeightedReindexExact where

------------------------------------------------------------------------
-- REPO CROSS-POLLINATION
--
-- The Navier--Stokes Galerkin lane already uses proof-relevant list
-- permutations to justify exact finite reindexing before taking a fold; see
-- NSTriadKNPhysicalOutputFiberPermutationRound35Exact and
-- NSTriadKNPhysicalGalerkinIncidencePermutationRound38Exact.
--
-- DASHI CONTRIBUTION
--
-- Extract the arithmetic-neutral core needed by the partition lane.  A finite
-- weighted count is invariant under an exact list permutation, and a mapped
-- enumeration may therefore be replaced by its target enumeration without
-- appealing to quotient cardinality, proof irrelevance, or analytic limits.
--
-- This is deliberately generic: the same kernel can be reused for partition
-- deletion fibres, finite spectral reindexings, incidence sums, and other
-- finite double-counting arguments.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; _+_)
open import Data.List.Base using (map)
import Data.List.Relation.Binary.Permutation.Propositional as Perm
import Data.Nat.Properties as NatP
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)

------------------------------------------------------------------------
-- Finite natural-valued folds.

foldNat : ∀ {A : Set} → (A → Nat) → List A → Nat
foldNat weight [] = 0
foldNat weight (x ∷ xs) = weight x + foldNat weight xs

foldMap :
  ∀ {A B : Set}
    (weight : B → Nat)
    (reindex : A → B)
    (items : List A) →
  foldNat weight (map reindex items)
  ≡ foldNat (λ item → weight (reindex item)) items
foldMap weight reindex [] = refl
foldMap weight reindex (x ∷ xs) =
  cong (weight (reindex x) +_) (foldMap weight reindex xs)

------------------------------------------------------------------------
-- Exact fold invariance under the standard proof-relevant permutation type.

foldPermutationInvariant :
  ∀ {A : Set}
    (weight : A → Nat)
    {left right : List A} →
  left Perm.↭ right →
  foldNat weight left ≡ foldNat weight right
foldPermutationInvariant weight Perm.refl = refl
foldPermutationInvariant weight (Perm.prep x permutation) =
  cong (weight x +_) (foldPermutationInvariant weight permutation)
foldPermutationInvariant weight
    (Perm.swap {ys = ys} x y permutation) =
  trans
    (cong
      (λ tail → weight x + (weight y + tail))
      (foldPermutationInvariant weight permutation))
    (trans
      (sym (NatP.+-assoc (weight x) (weight y) (foldNat weight ys)))
      (trans
        (cong
          (λ pairSum → pairSum + foldNat weight ys)
          (NatP.+-comm (weight x) (weight y)))
        (NatP.+-assoc (weight y) (weight x) (foldNat weight ys))))
foldPermutationInvariant weight (Perm.trans first second) =
  trans
    (foldPermutationInvariant weight first)
    (foldPermutationInvariant weight second)

------------------------------------------------------------------------
-- Mapped reindexing theorem used by fibre-count arguments.

mappedPermutationPreservesFold :
  ∀ {A B : Set}
    (weight : B → Nat)
    (reindex : A → B)
    (source : List A)
    {target : List B} →
  map reindex source Perm.↭ target →
  foldNat (λ item → weight (reindex item)) source
  ≡ foldNat weight target
mappedPermutationPreservesFold weight reindex source permutation =
  trans
    (sym (foldMap weight reindex source))
    (foldPermutationInvariant weight permutation)

------------------------------------------------------------------------
-- Constant-weight specialization: exact permutations preserve finite counts.

listLength : ∀ {A : Set} → List A → Nat
listLength [] = 0
listLength (_ ∷ xs) = 1 + listLength xs

foldOneIsLength :
  ∀ {A : Set} (items : List A) →
  foldNat (λ _ → 1) items ≡ listLength items
foldOneIsLength [] = refl
foldOneIsLength (_ ∷ xs) = cong (1 +_) (foldOneIsLength xs)

permutationPreservesLength :
  ∀ {A : Set} {left right : List A} →
  left Perm.↭ right →
  listLength left ≡ listLength right
permutationPreservesLength {left = left} {right = right} permutation =
  trans
    (sym (foldOneIsLength left))
    (trans
      (foldPermutationInvariant (λ _ → 1) permutation)
      (foldOneIsLength right))
