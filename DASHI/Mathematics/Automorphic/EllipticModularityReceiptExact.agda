module DASHI.Mathematics.Automorphic.EllipticModularityReceiptExact where

------------------------------------------------------------------------
-- ELLIPTIC MODULARITY RECEIPT -> FINITE SAME-OBJECT EULER AGREEMENT
--
-- The Modularity Theorem is known mathematics and is not reproved here.
-- This owner gives it an exact repository interface: one elliptic curve, one
-- global local-coefficient family, one weight-two modular form, and equality
-- of the actual good-prime coefficients.  From that receipt, all selected
-- good-prime local factors and every finite selected Euler denominator agree.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Rational.Base using (ℚ; _*_)

import DASHI.Mathematics.Arithmetic.EllipticCurveFrobeniusExact as Elliptic
import DASHI.Mathematics.Arithmetic.EllipticCurveGlobalLocalCoefficientExact as Global
import DASHI.Mathematics.Automorphic.TruncatedLFunctionExact as Truncated

record EllipticModularityReceipt
    (curve : Elliptic.ShortWeierstrassCurve)
    (family : Global.EllipticCurveGlobalLocalCoefficient curve) : Set₁ where
  field
    modularForm : Truncated.ModularFormFourierData

    goodPrimeCoefficientAgreement :
      (p : Agda.Builtin.Nat.Nat) →
      Global.GoodPrime family p →
      Global.frobeniusCoefficient (Global.localAtPrime family p)
      ≡ Truncated.coefficient
          (Truncated.ModularFormFourierData.modularCoefficients modularForm)
          (Global.primeNormFromGlobal family p)

    sourceBackedModularityTheorem : Set

open EllipticModularityReceipt public

modularLocalFactorAtGoodPrime :
  ∀ {curve family}
    (receipt : EllipticModularityReceipt curve family)
    (p : Agda.Builtin.Nat.Nat)
    (good : Global.GoodPrime family p)
    T →
  Global.localPolynomialValue (Global.localAtPrime family p) T
  ≡ Truncated.localEulerFactorValue
      (Truncated.ModularFormFourierData.modularCoefficients
        (modularForm receipt))
      (Global.primeNormFromGlobal family p)
      T
modularLocalFactorAtGoodPrime {family = family} receipt p good T =
  trans
    (sym
      (Global.goodPrimeLocalFactorIsGlobalPolynomial
        family p good T))
    (coefficientCongruence
      (goodPrimeCoefficientAgreement receipt p good))
  where
    sym : ∀ {A : Set} {x y : A} → x ≡ y → y ≡ x
    sym refl = refl

    trans : ∀ {A : Set} {x y z : A} →
      x ≡ y → y ≡ z → x ≡ z
    trans refl second = second

    coefficientCongruence :
      Global.frobeniusCoefficient (Global.localAtPrime family p)
      ≡ Truncated.coefficient
          (Truncated.ModularFormFourierData.modularCoefficients
            (modularForm receipt))
          (Global.primeNormFromGlobal family p) →
      Truncated.localEulerFactorValue
        (Global.goodPrimeCoefficientData family)
        (Global.primeNormFromGlobal family p)
        T
      ≡ Truncated.localEulerFactorValue
          (Truncated.ModularFormFourierData.modularCoefficients
            (modularForm receipt))
          (Global.primeNormFromGlobal family p)
          T
    coefficientCongruence refl = refl

record SelectedGoodPrime
    {curve : Elliptic.ShortWeierstrassCurve}
    (family : Global.EllipticCurveGlobalLocalCoefficient curve) : Set where
  constructor selected-good-prime
  field
    prime : Agda.Builtin.Nat.Nat
    good : Global.GoodPrime family prime

open SelectedGoodPrime public

selectedPrimeNorm :
  ∀ {curve family} →
  SelectedGoodPrime {curve = curve} family →
  Truncated.PrimeNorm
selectedPrimeNorm {family = family} selected =
  Global.primeNormFromGlobal family (prime selected)

mapSelectedPrimeNorm :
  ∀ {curve family} →
  List (SelectedGoodPrime {curve = curve} family) →
  List Truncated.PrimeNorm
mapSelectedPrimeNorm [] = []
mapSelectedPrimeNorm (selected ∷ rest) =
  selectedPrimeNorm selected ∷ mapSelectedPrimeNorm rest

globalSelectedGoodEulerDenominator :
  ∀ {curve}
    (family : Global.EllipticCurveGlobalLocalCoefficient curve) →
  ℚ →
  List (SelectedGoodPrime family) →
  ℚ
globalSelectedGoodEulerDenominator family T selected =
  Truncated.truncatedEulerDenominator
    (Global.goodPrimeCoefficientData family)
    T
    (mapSelectedPrimeNorm selected)

modularSelectedGoodEulerDenominator :
  ∀ {curve family}
    (receipt : EllipticModularityReceipt curve family) →
  ℚ →
  List (SelectedGoodPrime family) →
  ℚ
modularSelectedGoodEulerDenominator receipt T selected =
  Truncated.truncatedEulerDenominator
    (Truncated.ModularFormFourierData.modularCoefficients
      (modularForm receipt))
    T
    (mapSelectedPrimeNorm selected)

selectedGoodEulerProductsAgree :
  ∀ {curve family}
    (receipt : EllipticModularityReceipt curve family)
    T selected →
  globalSelectedGoodEulerDenominator family T selected
  ≡ modularSelectedGoodEulerDenominator receipt T selected
selectedGoodEulerProductsAgree receipt T [] = refl
selectedGoodEulerProductsAgree {family = family} receipt T (selected ∷ rest) =
  multiplyCongruence
    (coefficientFactorAgreement
      (goodPrimeCoefficientAgreement receipt
        (prime selected) (good selected)))
    (selectedGoodEulerProductsAgree receipt T rest)
  where
    multiplyCongruence : ∀ {a a' b b' : ℚ} →
      a ≡ a' → b ≡ b' → a * b ≡ a' * b'
    multiplyCongruence refl refl = refl

    coefficientFactorAgreement :
      Global.frobeniusCoefficient
        (Global.localAtPrime family (prime selected))
      ≡ Truncated.coefficient
          (Truncated.ModularFormFourierData.modularCoefficients
            (modularForm receipt))
          (selectedPrimeNorm selected) →
      Truncated.localEulerFactorValue
        (Global.goodPrimeCoefficientData family)
        (selectedPrimeNorm selected)
        T
      ≡ Truncated.localEulerFactorValue
          (Truncated.ModularFormFourierData.modularCoefficients
            (modularForm receipt))
          (selectedPrimeNorm selected)
          T
    coefficientFactorAgreement refl = refl
