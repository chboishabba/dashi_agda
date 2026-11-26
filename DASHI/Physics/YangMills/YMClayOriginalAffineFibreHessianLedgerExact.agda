module DASHI.Physics.YangMills.YMClayOriginalAffineFibreHessianLedgerExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- Tadeusz Bałaban,
-- "Renormalization Group Approach to Lattice Gauge Field Theories. I:
-- Generation of Effective Actions in a Small Field Approximation and a
-- Coupling Constant Renormalization in Four Dimensions",
-- Communications in Mathematical Physics 109 (1987), 249--301.
-- DOI: 10.1007/BF01215223.
--
-- Tadeusz Bałaban,
-- "Large Field Renormalization. I",
-- Communications in Mathematical Physics 122 (1989), 175--202.
-- DOI: 10.1007/BF01257412.
--
-- Tadeusz Bałaban,
-- "Large Field Renormalization. II",
-- Communications in Mathematical Physics 122 (1989), 355--392.
-- DOI: 10.1007/BF01238433.
--
-- DASHI CONTRIBUTION
--
-- Kernel-check the exact algebra of the original affine two-mark mass
--
--   K(W;s,t) = K0 + s KF + t KG + st KFG
--   A        = KF / K0
--   B        = KG / K0
--   R        = KFG / K0 - A B
--
-- namely
--
--   K(W;s,t) KFG - (KF + t KFG)(KG + s KFG) = K0 KFG - KF KG
--
-- and the normalized connected-covariance form
--
--   KFG/K - (KF_s/K)(KG_t/K) = (K0 KFG - KF KG)/K^2.
--
-- This is a DASHI algebraic ledger for global affine source marks.  It is
-- NOT a proof that this mass is the selected CMP122 Eq. (1.71) local
-- operation, NOT a CMP116 bond-valued J, and NOT an absolute spatial
-- rooted-shell estimate.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Data.Integer.Base as ℤ using (ℤ; +_)
open import Data.Nat.Base using (ℕ)
open import Data.Product using (_×_; _,_)
open import Data.Rational.Base as ℚ using
  (ℚ; 0ℚ; 1ℚ; _+_; _-_; _*_; _/_; 1/_; NonZero)
import Data.Rational.Properties as ℚP
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)

rat : (numerator : ℤ) (denominator : ℕ) .{{_ : Data.Nat.Base.NonZero denominator}} → ℚ
rat numerator denominator = ℚ._/_ numerator denominator

twoℚ : ℚ
twoℚ = 1ℚ + 1ℚ

affineRadius : ℚ
affineRadius = rat (+ 9) 100

affinePolydiscConstants :
    (1ℚ - twoℚ * affineRadius - affineRadius * affineRadius ≡ rat (+ 8119) 10000)
  × ((1ℚ - affineRadius) * (1ℚ - affineRadius) ≡ rat (+ 8281) 10000)
  × ((1ℚ + affineRadius) * (1ℚ + affineRadius) ≡ rat (+ 11881) 10000)
  × ((1ℚ - affineRadius * affineRadius)
      * (1ℚ - affineRadius * affineRadius) ≡ rat (+ 98386561) 100000000)
  × ((1ℚ - twoℚ * affineRadius - affineRadius * affineRadius)
      * (1ℚ - twoℚ * affineRadius - affineRadius * affineRadius)
      ≡ rat (+ 65918161) 100000000)
affinePolydiscConstants =
  let
    complexFloor :
      1ℚ - twoℚ * affineRadius - affineRadius * affineRadius ≡ rat (+ 8119) 10000
    complexFloor = ℚRing.solve-∀

    realLower :
      (1ℚ - affineRadius) * (1ℚ - affineRadius) ≡ rat (+ 8281) 10000
    realLower = ℚRing.solve-∀

    realUpper :
      (1ℚ + affineRadius) * (1ℚ + affineRadius) ≡ rat (+ 11881) 10000
    realUpper = ℚRing.solve-∀

    realHessianDenominator :
      (1ℚ - affineRadius * affineRadius)
        * (1ℚ - affineRadius * affineRadius) ≡ rat (+ 98386561) 100000000
    realHessianDenominator = ℚRing.solve-∀

    complexHessianDenominator :
      (1ℚ - twoℚ * affineRadius - affineRadius * affineRadius)
        * (1ℚ - twoℚ * affineRadius - affineRadius * affineRadius)
        ≡ rat (+ 65918161) 100000000
    complexHessianDenominator = ℚRing.solve-∀
  in
  complexFloor
    , realLower
    , realUpper
    , realHessianDenominator
    , complexHessianDenominator

affineMass :
  (k0 kf kg kfg s t : ℚ) →
  ℚ
affineMass k0 kf kg kfg s t =
  k0 + s * kf + t * kg + s * t * kfg

affineSMassDerivative :
  (kf kg kfg s t : ℚ) →
  ℚ
affineSMassDerivative kf kg kfg s t =
  kf + t * kfg

affineTMassDerivative :
  (kf kg kfg s t : ℚ) →
  ℚ
affineTMassDerivative kf kg kfg s t =
  kg + s * kfg

affineMassDeterminant :
  ∀ (k0 kf kg kfg s t : ℚ) →
    affineMass k0 kf kg kfg s t * kfg
      - affineSMassDerivative kf kg kfg s t
        * affineTMassDerivative kf kg kfg s t
    ≡ k0 * kfg - kf * kg
affineMassDeterminant k0 kf kg kfg s t =
  let
    determinant∀ :
      ∀ (a b c d x y : ℚ) →
        (a + x * b + y * c + x * y * d) * d
          - (b + y * d) * (c + x * d)
        ≡ a * d - b * c
    determinant∀ = ℚRing.solve-∀
  in
  determinant∀ k0 kf kg kfg s t

private
  covDeterminantWithInverse :
    ∀ (k0 kf kg kfg inv : ℚ) →
      k0 * inv ≡ 1ℚ →
    kfg * inv - (kf * inv) * (kg * inv)
      ≡ (k0 * kfg - kf * kg) * inv * inv
  covDeterminantWithInverse k0 kf kg kfg inv k0inv =
    let
      expand∀ :
        ∀ (a b c d i : ℚ) →
          (a * d - b * c) * i * i
            ≡ (a * d) * i * i - (b * c) * i * i
      expand∀ = ℚRing.solve-∀

      commuteInv∀ :
        ∀ (a b c d i : ℚ) →
          (a * d) * i * i - (b * c) * i * i
            ≡ d * (a * i) * i - (b * c) * i * i
      commuteInv∀ = ℚRing.solve-∀

      cancelInv∀ :
        ∀ (a b c d i : ℚ) →
          d * 1ℚ * i - (b * c) * i * i
            ≡ d * i - (b * i) * (c * i)
      cancelInv∀ = ℚRing.solve-∀
    in
    sym
      (trans
        (expand∀ k0 kf kg kfg inv)
        (trans
          (commuteInv∀ k0 kf kg kfg inv)
          (trans
            (cong
              (λ z → kfg * z * inv - (kf * kg) * inv * inv)
              k0inv)
            (cancelInv∀ kf kf kg kfg inv))))

affineConnectedCovarianceDeterminant :
  ∀ (k0 kf kg kfg : ℚ) .{{_ : NonZero k0}} →
    kfg * (1/ k0) - (kf * (1/ k0)) * (kg * (1/ k0))
      ≡ (k0 * kfg - kf * kg) * (1/ k0) * (1/ k0)
affineConnectedCovarianceDeterminant k0 kf kg kfg =
  covDeterminantWithInverse k0 kf kg kfg (1/ k0) (ℚP.*-inverseʳ k0)

affineTiltedConnectedCovarianceLedger :
  ∀ (k0 kf kg kfg s t : ℚ)
    .{{_ : NonZero (affineMass k0 kf kg kfg s t)}} →
    kfg * (1/ affineMass k0 kf kg kfg s t)
      - (affineSMassDerivative kf kg kfg s t
          * (1/ affineMass k0 kf kg kfg s t))
        * (affineTMassDerivative kf kg kfg s t
          * (1/ affineMass k0 kf kg kfg s t))
    ≡ (k0 * kfg - kf * kg)
      * (1/ affineMass k0 kf kg kfg s t)
      * (1/ affineMass k0 kf kg kfg s t)
affineTiltedConnectedCovarianceLedger k0 kf kg kfg s t =
  trans
    (affineConnectedCovarianceDeterminant
      (affineMass k0 kf kg kfg s t)
      (affineSMassDerivative kf kg kfg s t)
      (affineTMassDerivative kf kg kfg s t)
      kfg)
    (cong
      (λ z →
        z
          * (1/ affineMass k0 kf kg kfg s t)
          * (1/ affineMass k0 kf kg kfg s t))
      (affineMassDeterminant k0 kf kg kfg s t))
