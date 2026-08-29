module DASHI.Foundations.BishopFinitePermutationFoldExact where

------------------------------------------------------------------------
-- BISHOP-VALUED FINITE FOLDS RESPECT EXACT LIST PERMUTATIONS
--
-- Number-theory already owns the Nat-valued version.  This companion is the
-- analytic-neutral setoid analogue needed to reuse exact finite carrier
-- permutations after embedding weights into Bishop reals.
------------------------------------------------------------------------

open import Agda.Builtin.List using (List; []; _∷_)
import Data.List.Relation.Binary.Permutation.Propositional as Perm

import Real as BishopReal
import RealProperties as BishopP

open import DASHI.Physics.YangMills.CompactLieProofLevel

bishopFold : ∀ {A : Set} → (A → BishopReal.ℝ) → List A → BishopReal.ℝ
bishopFold weight [] = BishopReal.0ℝ
bishopFold weight (x ∷ xs) =
  BishopReal._+_ (weight x) (bishopFold weight xs)

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
