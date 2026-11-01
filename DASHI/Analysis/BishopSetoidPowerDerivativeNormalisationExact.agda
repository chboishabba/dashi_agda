module DASHI.Analysis.BishopSetoidPowerDerivativeNormalisationExact where

open import Agda.Builtin.Nat using (Nat; zero; suc)

import Real as Bishop
import RealProperties as BishopLaws

------------------------------------------------------------------------
-- BISHOP-SETOID POWER DERIVATIVE NORMALISATION
--
-- Setoid-native analogue of MarxPowerRuleNormalisation.  The recursive
-- product-rule derivative of x^n is normalized to repeated natural scaling of
-- x^(n-1) directly on the Bishop real carrier used by the elementary series.
------------------------------------------------------------------------

natScale : Nat → Bishop.ℝ → Bishop.ℝ
natScale zero value = Bishop.0ℝ
natScale (suc n) value = Bishop._+_ (natScale n value) value

natScaleCong :
  ∀ n {x y} → Bishop._≃_ x y → Bishop._≃_ (natScale n x) (natScale n y)
natScaleCong zero equality = BishopLaws.≃-refl
natScaleCong (suc n) equality =
  BishopLaws.+-cong (natScaleCong n equality) equality

natScaleMulRight :
  ∀ n x y →
  Bishop._≃_
    (Bishop._*_ (natScale n x) y)
    (natScale n (Bishop._*_ x y))
natScaleMulRight zero x y = BishopLaws.*-zeroˡ y
natScaleMulRight (suc n) x y =
  BishopLaws.≃-trans
    (BishopLaws.*-distribʳ-+ y (natScale n x) x)
    (BishopLaws.+-cong
      (natScaleMulRight n x y)
      BishopLaws.≃-refl)

powerDerivative : Nat → Bishop.ℝ → Bishop.ℝ
powerDerivative zero x = Bishop.0ℝ
powerDerivative (suc n) x =
  Bishop._+_
    (Bishop._*_ (powerDerivative n x) x)
    (Bishop.pow x n)

powerSuccessor :
  ∀ x n →
  Bishop._≃_
    (Bishop._*_ (Bishop.pow x n) x)
    (Bishop.pow x (suc n))
powerSuccessor x n = BishopLaws.≃-refl

powerDerivativeNatScale :
  ∀ n x →
  Bishop._≃_
    (powerDerivative (suc n) x)
    (natScale (suc n) (Bishop.pow x n))
powerDerivativeNatScale zero x =
  BishopLaws.≃-trans
    (BishopLaws.+-cong
      (BishopLaws.*-zeroˡ x)
      BishopLaws.≃-refl)
    (BishopLaws.≃-trans
      (BishopLaws.+-identityˡ (Bishop.pow x zero))
      (BishopLaws.≃-symm
        (BishopLaws.+-identityˡ (Bishop.pow x zero))))
powerDerivativeNatScale (suc n) x =
  BishopLaws.≃-trans
    (BishopLaws.+-cong
      (BishopLaws.*-cong
        (powerDerivativeNatScale n x)
        BishopLaws.≃-refl)
      BishopLaws.≃-refl)
    (BishopLaws.≃-trans
      (BishopLaws.+-cong
        (natScaleMulRight (suc n) (Bishop.pow x n) x)
        BishopLaws.≃-refl)
      (BishopLaws.≃-trans
        (BishopLaws.+-cong
          (natScaleCong (suc n) (powerSuccessor x n))
          (powerSuccessor x n))
        BishopLaws.≃-refl))
