module DASHI.Foundations.BishopFinitePermutationFoldExact where

------------------------------------------------------------------------
-- BISHOP-VALUED FINITE FOLDS RESPECT EXACT LIST PERMUTATIONS
------------------------------------------------------------------------

open import Agda.Builtin.List using (List; []; _∷_)
open import Data.List.Base using (map; _++_)
import Data.List.Relation.Binary.Permutation.Propositional as Perm

import Real as BishopReal
import RealProperties as BishopP

open import DASHI.Physics.YangMills.CompactLieProofLevel

bishopFold : ∀ {A : Set} → (A → BishopReal.ℝ) → List A → BishopReal.ℝ
bishopFold weight [] = BishopReal.0ℝ
bishopFold weight (x ∷ xs) =
  BishopReal._+_ (weight x) (bishopFold weight xs)

bishopFoldAppend :
  ∀ {A : Set}
    (weight : A → BishopReal.ℝ) →
  ∀ xs ys →
  BishopReal._≃_
    (bishopFold weight (xs ++ ys))
    (BishopReal._+_
      (bishopFold weight xs)
      (bishopFold weight ys))
bishopFoldAppend weight [] ys =
  BishopP.≃-symm (BishopP.+-identityˡ (bishopFold weight ys))
bishopFoldAppend weight (x ∷ xs) ys =
  BishopP.≃-trans
    (BishopP.+-congˡ
      (weight x)
      (bishopFoldAppend weight xs ys))
    (BishopP.≃-symm
      (BishopP.+-assoc
        (weight x)
        (bishopFold weight xs)
        (bishopFold weight ys)))

bishopFoldMap :
  ∀ {A B : Set}
    (weight : B → BishopReal.ℝ)
    (f : A → B) →
  ∀ xs →
  BishopReal._≃_
    (bishopFold weight (map f xs))
    (bishopFold (λ x → weight (f x)) xs)
bishopFoldMap weight f [] = BishopP.≃-refl
bishopFoldMap weight f (x ∷ xs) =
  BishopP.+-congˡ
    (weight (f x))
    (bishopFoldMap weight f xs)

bishopFoldPointwise :
  ∀ {A : Set}
    (left right : A → BishopReal.ℝ) →
  ∀ xs →
  (∀ x → BishopReal._≤_ (left x) (right x)) →
  BishopReal._≤_
    (bishopFold left xs)
    (bishopFold right xs)
bishopFoldPointwise left right [] pointwise = BishopP.≤-refl
bishopFoldPointwise left right (x ∷ xs) pointwise =
  BishopP.+-mono-≤
    (pointwise x)
    (bishopFoldPointwise left right xs pointwise)

bishopFoldPermutationInvariant :
  ∀ {A : Set}
    (weight : A → BishopReal.ℝ)
    {left right : List A} →
  left Perm.↭ right →
  BishopReal._≃_
    (bishopFold weight left)
    (bishopFold weight right)
bishopFoldPermutationInvariant weight Perm.refl = BishopP.≃-refl
bishopFoldPermutationInvariant weight (Perm.prep x permutation) =
  BishopP.+-congˡ
    (weight x)
    (bishopFoldPermutationInvariant weight permutation)
bishopFoldPermutationInvariant weight
    (Perm.swap {ys = ys} x y permutation) =
  BishopP.≃-trans
    (BishopP.+-congˡ
      (weight x)
      (BishopP.+-congˡ
        (weight y)
        (bishopFoldPermutationInvariant weight permutation)))
    (let open BishopP.ℝ-Solver
     in solve 3
       (λ x′ y′ tail →
         x′ ⊕ (y′ ⊕ tail)
         ⊜ y′ ⊕ (x′ ⊕ tail))
       BishopP.≃-refl
       (weight x) (weight y) (bishopFold weight ys))
bishopFoldPermutationInvariant weight (Perm.trans first second) =
  BishopP.≃-trans
    (bishopFoldPermutationInvariant weight first)
    (bishopFoldPermutationInvariant weight second)

bishopFinitePermutationFoldLevel : ProofLevel
bishopFinitePermutationFoldLevel = machineChecked
