module DASHI.Analysis.BishopPowerFirstOrderDifferenceFactorisationExact where

open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Rational.Unnormalised using (0ℚᵘ; 1ℚᵘ)

import Real as Bishop
import RealProperties as BishopP

import DASHI.Analysis.BishopSetoidPowerDerivativeNormalisationExact as Power

------------------------------------------------------------------------
-- BISHOP POWER FIRST-ORDER DIFFERENCE FACTORISATION
--
-- Define Q_n(x,h) recursively by
--
--   Q_0 = 0,
--   Q_{n+1} = Q_n (x+h) + x^n.
--
-- Then, entirely algebraically on the Bishop setoid carrier,
--
--   (x+h)^n - x^n ~= h Q_n(x,h).
--
-- At h=0 the quotient polynomial reduces to the already-owned natural-scale
-- derivative coefficient.  No division by h and no analytic limit enter this
-- owner.
------------------------------------------------------------------------

powerDifferenceQuotient : Bishop.ℝ → Bishop.ℝ → Nat → Bishop.ℝ
powerDifferenceQuotient x h zero = Bishop.0ℝ
powerDifferenceQuotient x h (suc n) =
  Bishop._+_
    (Bishop._*_
      (powerDifferenceQuotient x h n)
      (Bishop._+_ x h))
    (Bishop.pow x n)

powerDifferenceFactorisation :
  ∀ x h n →
  Bishop._≃_
    (Bishop._-_
      (Bishop.pow (Bishop._+_ x h) n)
      (Bishop.pow x n))
    (Bishop._*_ h (powerDifferenceQuotient x h n))
powerDifferenceFactorisation x h zero =
  let open BishopP.ℝ-Solver
  in solve 1
    (λ h′ → Κ 1ℚᵘ ⊖ Κ 1ℚᵘ ⊜ h′ ⊗ Κ 0ℚᵘ)
    BishopP.≃-refl h
powerDifferenceFactorisation x h (suc n) =
  let
    y = Bishop._+_ x h
    q = powerDifferenceQuotient x h n
    xn = Bishop.pow x n
    yn = Bishop.pow y n
    open BishopP.ℝ-Solver
  in
  BishopP.≃-trans
    (solve 5
      (λ yn′ y′ xn′ x′ h′ →
        (yn′ ⊗ y′) ⊖ (xn′ ⊗ x′)
        ⊜ ((yn′ ⊖ xn′) ⊗ y′) ⊕ (xn′ ⊗ h′))
      BishopP.≃-refl
      yn y xn x h)
    (BishopP.≃-trans
      (BishopP.+-cong
        (BishopP.*-congʳ (powerDifferenceFactorisation x h n))
        BishopP.≃-refl)
      (solve 4
        (λ h′ q′ y′ xn′ →
          (h′ ⊗ q′) ⊗ y′ ⊕ (xn′ ⊗ h′)
          ⊜ h′ ⊗ ((q′ ⊗ y′) ⊕ xn′))
        BishopP.≃-refl
        h q y xn))

quotientAtZero :
  ∀ x n →
  Bishop._≃_
    (powerDifferenceQuotient x Bishop.0ℝ (suc n))
    (Power.natScale (suc n) (Bishop.pow x n))
quotientAtZero x zero =
  let open BishopP.ℝ-Solver
  in solve 1
    (λ x′ → (Κ 0ℚᵘ ⊗ (x′ ⊕ Κ 0ℚᵘ)) ⊕ Κ 1ℚᵘ ⊜ Κ 1ℚᵘ)
    BishopP.≃-refl x
quotientAtZero x (suc n) =
  let
    oldPower = Bishop.pow x n
    nextPower = Bishop.pow x (suc n)
  in
  BishopP.≃-trans
    (BishopP.+-cong
      (BishopP.*-cong
        (quotientAtZero x n)
        (BishopP.+-identityʳ x))
      BishopP.≃-refl)
    (BishopP.≃-trans
      (BishopP.+-cong
        (BishopP.≃-trans
          (Power.natScaleMulRight (suc n) oldPower x)
          (Power.natScaleCong (suc n) (Power.powerSuccessor x n)))
        (Power.powerSuccessor x n))
      BishopP.≃-refl)

------------------------------------------------------------------------
-- The quotient-at-zero theorem has the same displayed normal form as the
-- algebraic power derivative.  Same-object identification is now explicit.
------------------------------------------------------------------------

powerDerivativeIsDifferenceQuotientAtZero :
  ∀ x n →
  Bishop._≃_
    (Power.powerDerivative (suc n) x)
    (powerDifferenceQuotient x Bishop.0ℝ (suc n))
powerDerivativeIsDifferenceQuotientAtZero x n =
  BishopP.≃-trans
    (Power.powerDerivativeNatScale n x)
    (BishopP.≃-symm (quotientAtZero x n))

record Status : Set where
  field
    exactPowerDifferenceFactorisationOwned : Bool
    quotientAtZeroNormalisationOwned : Bool
    algebraicDerivativeDifferenceQuotientWeldOwned : Bool
    quotientContinuityAtZeroClosed : Bool

    exactPowerDifferenceFactorisationOwnedIsTrue : exactPowerDifferenceFactorisationOwned ≡ true
    quotientAtZeroNormalisationOwnedIsTrue : quotientAtZeroNormalisationOwned ≡ true
    algebraicDerivativeDifferenceQuotientWeldOwnedIsTrue :
      algebraicDerivativeDifferenceQuotientWeldOwned ≡ true
    quotientContinuityAtZeroClosedIsFalse : quotientContinuityAtZeroClosed ≡ false

open Status public

canonicalStatus : Status
canonicalStatus = record
  { exactPowerDifferenceFactorisationOwned = true
  ; quotientAtZeroNormalisationOwned = true
  ; algebraicDerivativeDifferenceQuotientWeldOwned = true
  ; quotientContinuityAtZeroClosed = false
  ; exactPowerDifferenceFactorisationOwnedIsTrue = refl
  ; quotientAtZeroNormalisationOwnedIsTrue = refl
  ; algebraicDerivativeDifferenceQuotientWeldOwnedIsTrue = refl
  ; quotientContinuityAtZeroClosedIsFalse = refl
  }
