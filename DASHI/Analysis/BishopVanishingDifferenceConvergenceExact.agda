module DASHI.Analysis.BishopVanishingDifferenceConvergenceExact where

------------------------------------------------------------------------
-- VANISHING-DIFFERENCE CONVERGENCE TRANSPORT ON BISHOP REALS
--
-- DASHI CONTRIBUTION
--
-- If
--
--   right_n -> L,
--   error_n -> 0,
--   |left_n - right_n| <= |error_n|,
--
-- then left_n -> L.
--
-- This is the quantitative glue needed by the finite Cauchy-wing estimate.
-- It is proved directly from the pinned Bishop convergence definition.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat; suc; _*_)
import Data.Nat.Properties as NatP
open import Data.Integer.Base using (+_)
open import Data.Product.Base using (proj₁; proj₂)
open import Data.Rational.Unnormalised as Rat using (_/_)
import Data.Rational.Unnormalised.Properties as RatP

import Real as BishopReal
import RealProperties as BishopP
import Sequence as BishopSequence

vanishingDifferenceConvergence :
  ∀ {left right error : Nat → BishopReal.ℝ}
    {limit : BishopReal.ℝ} →
  BishopSequence._ConvergesTo_ right limit →
  BishopSequence._ConvergesTo_ error BishopReal.0ℝ →
  (∀ index →
    BishopReal._≤_
      (BishopReal.∣ BishopReal._-_ (left index) (right index) ∣)
      (BishopReal.∣ error index ∣)) →
  BishopSequence._ConvergesTo_ left limit
vanishingDifferenceConvergence
    {left} {right} {error} {limit}
    (BishopSequence.con* rightConverges)
    (BishopSequence.con* errorConverges)
    differenceBound =
  BishopSequence.con*
    (λ
      { (suc k-1) →
        let
          k = suc k-1
          precision = 2 * k

          rightCutoff = suc (proj₁ (rightConverges precision))
          errorCutoff = suc (proj₁ (errorConverges precision))
          cutoff = rightCutoff NatP.⊔ errorCutoff

          halfPlusHalf :
            BishopReal._≃_
              (BishopReal._+_
                (((+ 1 / precision)) BishopReal.⋆)
                (((+ 1 / precision)) BishopReal.⋆))
              (((+ 1 / k)) BishopReal.⋆)
          halfPlusHalf =
            BishopP.≃-trans
              (BishopP.≃-symm
                (BishopP.⋆-distrib-+
                  (+ 1 / precision)
                  (+ 1 / precision)))
              (BishopP.⋆-cong
                (RatP.*≡*
                  (let open BishopP.ℤ-Solver
                   in solve 1
                     (λ k′ →
                       ((Κ (+ 1) ⊗ (Κ (+ 2) ⊗ k′)) ⊕
                        (Κ (+ 1) ⊗ (Κ (+ 2) ⊗ k′))) ⊗ k′
                       ⊜
                       Κ (+ 1) ⊗
                         ((Κ (+ 2) ⊗ k′) ⊗
                          (Κ (+ 2) ⊗ k′)))
                     refl
                     (+ k))))
        in
        NatP.pred cutoff ,
        λ
          { (suc n-1) cutoff≤n →
            let
              n = suc n-1

              errorAtN :
                BishopReal._≤_
                  (BishopReal.∣ error n ∣)
                  (((+ 1 / precision)) BishopReal.⋆)
              errorAtN =
                BishopP.≤-respˡ-≃
                  (BishopP.≃-trans
                    (BishopP.∣-∣-cong
                      (BishopP.≃-symm
                        (BishopP.+-identityʳ (error n))))
                    (BishopP.∣-∣-cong
                      (BishopP.+-cong
                        BishopP.≃-refl
                        (BishopP.≃-symm
                          (BishopP.-‿cong
                            (BishopP.≃-symm
                              (BishopP.+-inverseʳ BishopReal.0ℝ)))))))
                  (proj₂ (errorConverges precision)
                    n
                    (NatP.≤-trans
                      (NatP.m≤n⊔m rightCutoff errorCutoff)
                      cutoff≤n))

              rightAtN :
                BishopReal._≤_
                  (BishopReal.∣
                    BishopReal._-_ (right n) limit
                  ∣)
                  (((+ 1 / precision)) BishopReal.⋆)
              rightAtN =
                proj₂ (rightConverges precision)
                  n
                  (NatP.≤-trans
                    (NatP.m≤m⊔n rightCutoff errorCutoff)
                    cutoff≤n)
            in
            let open BishopP.≤-Reasoning
            in begin
              BishopReal.∣ BishopReal._-_ (left n) limit ∣
                ≈⟨ BishopP.∣-∣-cong
                    (let open BishopP.ℝ-Solver
                     in solve 3
                       (λ leftN rightN limitN →
                         (leftN ⊖ limitN)
                         ⊜
                         ((leftN ⊖ rightN) ⊕
                          (rightN ⊖ limitN)))
                       BishopP.≃-refl
                       (left n) (right n) limit) ⟩
              BishopReal.∣
                BishopReal._+_
                  (BishopReal._-_ (left n) (right n))
                  (BishopReal._-_ (right n) limit)
              ∣
                ≤⟨ BishopP.∣x+y∣≤∣x∣+∣y∣
                    (BishopReal._-_ (left n) (right n))
                    (BishopReal._-_ (right n) limit) ⟩
              BishopReal._+_
                (BishopReal.∣
                  BishopReal._-_ (left n) (right n)
                ∣)
                (BishopReal.∣
                  BishopReal._-_ (right n) limit
                ∣)
                ≤⟨ BishopP.+-mono-≤
                    (BishopP.≤-trans
                      (differenceBound n)
                      errorAtN)
                    rightAtN ⟩
              BishopReal._+_
                (((+ 1 / precision)) BishopReal.⋆)
                (((+ 1 / precision)) BishopReal.⋆)
                ≈⟨ halfPlusHalf ⟩
              (((+ 1 / k)) BishopReal.⋆)
                ∎
          }
      }
    )
