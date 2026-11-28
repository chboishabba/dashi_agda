module DASHI.Foundations.BishopFiniteCauchyWeightedPowerExact where

------------------------------------------------------------------------
-- General original Bishop-real FINITE weighted Cauchy power identity.
-- For arbitrary signed X and arbitrary coefficient functions a,b:
--
--   (sum_{k<=n} a_k b_(n-k)) X^n
--     ~= sum_{k<=n} (a_k X^k)(b_(n-k) X^(n-k)).
--
-- No formal infinite series, factorial assumptions or postulates.
-- Actual original Fin(suc n) index, bounded Nat difference, Bishop
-- native right-multiplying power and semiring finite-sum congruence.
-- Source-written; pinned Agda 2.9 typecheck is still outstanding.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Fin.Base using (Fin; toℕ)
import Data.Fin.Properties as FinP
import Data.Nat.Base as N
open N using (z≤n; s≤s)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)
open import Data.Integer.Base using (+_)
open import Data.Rational.Unnormalised using (0ℚᵘ; 1ℚᵘ; _/_)

import Algebra.Properties.Semiring.Sum as SemiringSum
import Real as R
import RealProperties as P
import DASHI.Foundations.BishopFiniteCauchyRowReindexExact as Row

module BishopSum = SemiringSum P.+-*-semiring

boundedIndexPlusDifference :
  ∀ (n k : Nat) → k N.≤ n →
  k N.+ (n N.∸ k) ≡ n
boundedIndexPlusDifference zero zero _ = refl
boundedIndexPlusDifference zero (suc k) ()
boundedIndexPlusDifference (suc n) zero _ = refl
boundedIndexPlusDifference (suc n) (suc k) (s≤s h) =
  cong suc (boundedIndexPlusDifference n k h)

-- Native Bishop pow multiplies to the RIGHT. Induct on the first
-- exponent, matching the Agda Nat addition recursion.
bishopPowerAddition : ∀ X i j →
  R._≃_
    (R.pow X (i N.+ j))
    (R._*_ (R.pow X i) (R.pow X j))
bishopPowerAddition X zero j =
  P.≃-symm (P.*-identityˡ (R.pow X j))
bishopPowerAddition X (suc i) j =
  P.≃-trans
    (P.*-congʳ (bishopPowerAddition X i j))
    (let
       p = R.pow X i
       q = R.pow X j
       open P.ℝ-Solver
     in solve 3
       (λ p q x → (p ⊗ q) ⊗ x ⊜ (p ⊗ x) ⊗ q)
       P.≃-refl p q X)

bishopFinBoundedPowerSplit :
  ∀ X n (index : Fin (suc n)) →
  R._≃_
    (R._*_ (R.pow X (toℕ index))
      (R.pow X (n N.∸ toℕ index)))
    (R.pow X n)
bishopFinBoundedPowerSplit X n index =
  P.≃-trans
    (P.≃-symm
      (bishopPowerAddition X (toℕ index) (n N.∸ toℕ index)))
    (P.≃-refl₂
      (cong (R.pow X)
        (boundedIndexPlusDifference n (toℕ index)
          (FinP.toℕ≤pred[n] index))))

-- One original stdlib finite-sum congruence for arbitrary coefficient
-- sequences, not merely the particular exponential coefficient source.
bishopFiniteWeightedCauchy :
  ∀ left right X n →
  R._≃_
    (R._*_
      (Row.cauchyCoefficient left right n)
      (R.pow X n))
    (Row.cauchyCoefficient
      (λ k → R._*_ (left k) (R.pow X k))
      (λ k → R._*_ (right k) (R.pow X k))
      n)
bishopFiniteWeightedCauchy left right X n =
  P.≃-trans
    (BishopSum.*-distribʳ-sum
      (R.pow X n)
      (λ index →
        R._*_
          (left (toℕ index))
          (right (n N.∸ toℕ index))))
    (BishopSum.sum-cong-≋
      (λ index →
        let
          k = toℕ index
          m = n N.∸ k
          a = left k
          b = right m
          p = R.pow X k
          q = R.pow X m
          open P.ℝ-Solver
        in
        P.≃-trans
          (P.*-congˡ
            (P.≃-symm (bishopFinBoundedPowerSplit X n index)))
          (solve 4
            (λ a b p q →
              (a ⊗ b) ⊗ (p ⊗ q)
                ⊜ (a ⊗ p) ⊗ (b ⊗ q))
            P.≃-refl a b p q)))
