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
open import Data.Rational.Unnormalised as Rat using (ℚᵘ; 0ℚᵘ; _/_)
import Data.Rational.Unnormalised.Properties as RatP
open import NonReflectiveZ as ZSolver using ()
  renaming
    ( solve to Zsolve
    ; _⊕_ to _:+_
    ; _⊗_ to _:*_
    ; _⊜_ to _:=_
    ; Κ to ZK
    )

import Real as BishopReal
import RealProperties as BishopP
import Sequence as BishopSequence

embed : ℚᵘ → BishopReal.ℝ
embed = BishopReal._⋆

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
                embed (+ 1 / precision)
                embed (+ 1 / precision))
              embed (+ 1 / k)
          halfPlusHalf =
            BishopP.≃-trans
              (BishopP.≃-symm
                (BishopP.⋆-distrib-+
                  (+ 1 / precision)
                  (+ 1 / precision)))
              (BishopP.⋆-cong
                (RatP.*≡*
                  (Zsolve 1
                    (λ k′ →
                      ((ZK (+ 1) :* (ZK (+ 2) :* k′)) :+
                       (ZK (+ 1) :* (ZK (+ 2) :* k′))) :* k′
                      :=
                      ZK (+ 1) :*
                        ((ZK (+ 2) :* k′) :*
                         (ZK (+ 2) :* k′)))
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
                  embed (+ 1 / precision)
              errorAtN =
                BishopP.≤-respˡ-≃
                  (BishopP.∣-∣-cong
                    (let open BishopP.ℝ-Solver
                     in solve 1
                       (λ value → value ⊜ value ⊖ Κ Rat.0ℚᵘ)
                       BishopP.≃-refl
                       (error n)))
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
                  embed (+ 1 / precision)
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
                embed (+ 1 / precision)
                embed (+ 1 / precision)
                ≈⟨ halfPlusHalf ⟩
              embed (+ 1 / k)
                ∎
          }
      }
    )
