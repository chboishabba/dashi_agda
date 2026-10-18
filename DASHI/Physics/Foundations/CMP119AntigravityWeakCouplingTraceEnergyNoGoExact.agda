{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.CMP119AntigravityWeakCouplingTraceEnergyNoGoExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational.Base using
  (ℚ; 0ℚ; 1ℚ; _+_; _-_; _*_; _≤_; -_)
import Data.Rational.Properties as ℚP
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using (subst; sym)

------------------------------------------------------------------------
-- AG-S4 / WEAK-COUPLING TRACE-ANOMALY REPULSION NO-GO
--
-- Write a positive anomaly magnitude coefficient kappa >= 0 and encode
--
--   g^{-2} = 2 kappa + margin,   margin >= 0.
--
-- Thus 2 kappa <= g^{-2}.  For nonnegative electric/magnetic squares:
--
--   2 rho = g^{-2} (E2 + B2)
--   Theta = - 2 kappa (B2 - E2)
--   A = Theta + 2 rho.
--
-- Exact algebra gives
--
--   A = (4 kappa + margin) E2 + margin B2 >= 0.
--
-- Hence the anomaly route cannot produce negative active stress anywhere in
-- this coefficient regime.  Repulsion would require leaving this regime or
-- changing the source decomposition.
------------------------------------------------------------------------

record WeakCouplingYMTraceEnergyData : Set where
  field
    kappa : ℚ
    margin : ℚ
    electricSquare : ℚ
    magneticSquare : ℚ

    kappaNonnegative : 0ℚ ≤ kappa
    marginNonnegative : 0ℚ ≤ margin
    electricSquareNonnegative : 0ℚ ≤ electricSquare
    magneticSquareNonnegative : 0ℚ ≤ magneticSquare

open WeakCouplingYMTraceEnergyData public

two : ℚ
two = 1ℚ + 1ℚ

four : ℚ
four = two + two

inverseCoupling : WeakCouplingYMTraceEnergyData → ℚ
inverseCoupling d = two * kappa d + margin d

twiceEnergyDensity : WeakCouplingYMTraceEnergyData → ℚ
twiceEnergyDensity d =
  inverseCoupling d * (electricSquare d + magneticSquare d)

lorentzianTraceAnomaly : WeakCouplingYMTraceEnergyData → ℚ
lorentzianTraceAnomaly d =
  - (two * kappa d * (magneticSquare d - electricSquare d))

activeStress : WeakCouplingYMTraceEnergyData → ℚ
activeStress d =
  lorentzianTraceAnomaly d + twiceEnergyDensity d

activeStressWeakCouplingDecomposition :
  ∀ d →
  activeStress d
  ≡
  (four * kappa d + margin d) * electricSquare d
    + margin d * magneticSquare d
activeStressWeakCouplingDecomposition d =
  ℚRing.solve-∀
    (kappa d) (margin d) (electricSquare d) (magneticSquare d)

twoNonnegative : 0ℚ ≤ two
twoNonnegative =
  ℚP.<⇒≤
    (ℚP.+-mono-<-<
      (ℚP.positive⁻¹ 1ℚ)
      (ℚP.positive⁻¹ 1ℚ))

fourNonnegative : 0ℚ ≤ four
fourNonnegative =
  ℚP.+-mono-≤ twoNonnegative twoNonnegative

activeStressNonnegative :
  ∀ d → 0ℚ ≤ activeStress d
activeStressNonnegative d =
  let
    fourKappaNN :
      0ℚ ≤ four * kappa d
    fourKappaNN =
      ℚP.*-mono-≤
        fourNonnegative
        (kappaNonnegative d)
        ℚP.≤-refl
        ℚP.≤-refl

    electricCoefficientNN :
      0ℚ ≤ four * kappa d + margin d
    electricCoefficientNN =
      ℚP.+-mono-≤ fourKappaNN (marginNonnegative d)

    electricTermNN :
      0ℚ ≤
      (four * kappa d + margin d) * electricSquare d
    electricTermNN =
      ℚP.*-mono-≤
        electricCoefficientNN
        (electricSquareNonnegative d)
        ℚP.≤-refl
        ℚP.≤-refl

    magneticTermNN :
      0ℚ ≤ margin d * magneticSquare d
    magneticTermNN =
      ℚP.*-mono-≤
        (marginNonnegative d)
        (magneticSquareNonnegative d)
        ℚP.≤-refl
        ℚP.≤-refl

    sumNN :
      0ℚ ≤
      (four * kappa d + margin d) * electricSquare d
        + margin d * magneticSquare d
    sumNN =
      ℚP.+-mono-≤ electricTermNN magneticTermNN
  in
  subst
    (λ value → 0ℚ ≤ value)
    (sym (activeStressWeakCouplingDecomposition d))
    sumNN

weakCouplingTraceAnomalyCanGiveNegativeActiveStress : Bool
weakCouplingTraceAnomalyCanGiveNegativeActiveStress = false

weakCouplingTraceAnomalyCanGiveNegativeActiveStressIsFalse :
  weakCouplingTraceAnomalyCanGiveNegativeActiveStress ≡ false
weakCouplingTraceAnomalyCanGiveNegativeActiveStressIsFalse = refl

strongCoefficientOrNonstandardSourceRequiredForAnomalyRepulsion : Bool
strongCoefficientOrNonstandardSourceRequiredForAnomalyRepulsion = true

strongCoefficientOrNonstandardSourceRequiredForAnomalyRepulsionIsTrue :
  strongCoefficientOrNonstandardSourceRequiredForAnomalyRepulsion ≡ true
strongCoefficientOrNonstandardSourceRequiredForAnomalyRepulsionIsTrue = refl
