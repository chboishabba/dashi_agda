module DASHI.Physics.YangMills.BalabanInverseSquareIntervalIdentity where

-- Arbitrary-interval form of Bałaban's inverse-square coupling recurrence.
--
-- From
--
--   u_{j+1} = u_j - β_{j+1}
--
-- this module proves
--
--   u_{k+n} = u_k - Σ_{j=k+1}^{k+n} β_j
--
-- and transports bilateral beta-interval estimates to the corresponding
-- inverse-square enclosure.  The proof uses only the existing named additive
-- arithmetic socket; no beta estimate is introduced.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Nat.Base using (ℕ; zero; suc; _+_)
open import Data.Product using (_×_; _,_)

open import DASHI.Foundations.RealAnalysisAxioms using
  ( ℝ
  ; _-ℝ_
  ; _≤ℝ_
  ; cong
  ; trans
  )
open import DASHI.Physics.YangMills.BalabanEffectiveCouplingTrajectory using
  ( BalabanInverseSquareCouplingStep
  ; inverseSquaredCoupling
  ; betaCorrection
  ; exactInverseSquareUpdate
  )
open import DASHI.Physics.YangMills.BalabanInverseSquareCouplingBudget using
  ( InverseSquareBudgetArithmetic
  ; sub-zero
  ; sub-assoc-right
  ; subtract-right-antitone
  )
open import DASHI.Physics.YangMills.BalabanIntervalDeterminantAlgebra using
  ( intervalSum )

sym : {A : Set} → {x y : A} → x ≡ y → y ≡ x
sym refl = refl

inverseSquareIntervalTelescoping :
  (arith : InverseSquareBudgetArithmetic) →
  (step : BalabanInverseSquareCouplingStep) →
  ∀ k n →
  inverseSquaredCoupling step (n + k)
    ≡ inverseSquaredCoupling step k
        -ℝ intervalSum (betaCorrection step) k n
inverseSquareIntervalTelescoping arith step k zero =
  sym (sub-zero arith (inverseSquaredCoupling step k))
inverseSquareIntervalTelescoping arith step k (suc n) =
  trans
    (exactInverseSquareUpdate step (n + k))
    (trans
      (cong
        (λ u → u -ℝ betaCorrection step (suc (n + k)))
        (inverseSquareIntervalTelescoping arith step k n))
      (sub-assoc-right arith
        (inverseSquaredCoupling step k)
        (intervalSum (betaCorrection step) k n)
        (betaCorrection step (suc (n + k)))))

replaceLeft :
  ∀ {a b c : ℝ} →
  a ≡ b →
  b ≤ℝ c →
  a ≤ℝ c
replaceLeft refl b≤c = b≤c

replaceRight :
  ∀ {a b c : ℝ} →
  a ≤ℝ b →
  b ≡ c →
  a ≤ℝ c
replaceRight a≤b refl = a≤b

-- If lower ≤ Σβ ≤ upper, then antitonicity of subtraction gives
--
--   u_k - upper ≤ u_{k+n} ≤ u_k - lower.
inverseSquareIntervalEnclosure :
  (arith : InverseSquareBudgetArithmetic) →
  (step : BalabanInverseSquareCouplingStep) →
  (lower upper : ℕ → ℕ → ℝ) →
  (lowerBound :
    ∀ k n →
    lower k n
      ≤ℝ intervalSum (betaCorrection step) k n) →
  (upperBound :
    ∀ k n →
    intervalSum (betaCorrection step) k n
      ≤ℝ upper k n) →
  ∀ k n →
  (inverseSquaredCoupling step k -ℝ upper k n
      ≤ℝ inverseSquaredCoupling step (n + k))
  ×
  (inverseSquaredCoupling step (n + k)
      ≤ℝ inverseSquaredCoupling step k -ℝ lower k n)
inverseSquareIntervalEnclosure
  arith step lower upper lowerBound upperBound k n =
  replaceRight
    (subtract-right-antitone arith (upperBound k n))
    (sym (inverseSquareIntervalTelescoping arith step k n))
  ,
  replaceLeft
    (inverseSquareIntervalTelescoping arith step k n)
    (subtract-right-antitone arith (lowerBound k n))
