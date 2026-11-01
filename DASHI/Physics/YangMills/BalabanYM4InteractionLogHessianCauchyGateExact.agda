{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanYM4InteractionLogHessianCauchyGateExact where

------------------------------------------------------------------------
-- ROW A: ONE NORMALIZED-INTERACTION DERIVATIVE PACKAGE -> THE O(g) CONSTANT C
--
-- PRIMARY SOURCE
--
-- Tadeusz Bałaban,
-- "Renormalization Group Approach to Lattice Gauge Field Theories. I.",
-- Communications in Mathematical Physics 109 (1987), 249--301.
-- DOI: 10.1007/BF01215223.
--
-- CMP109 writes the nonlinear fluctuation contribution as the logarithm of a
-- normalized interaction integral.  Along a background direction let
--
--      Z = Z_int,  Z1 = dZ,  Z2 = d^2 Z.
--
-- Then
--
--      d^2 log Z = (Z Z2 - Z1^2) / Z^2.
--
-- If
--
--      z0 <= Z <= z1,       |Z1| <= A g,       |Z2| <= B g,
--      0 <= g <= gamma,     z0 > 0,
--
-- this file proves the explicit bound
--
--      |d^2 log Z| <= C g,
--      C = (z1 B + A^2 gamma) / z0^2.
--
-- Thus A2 is reduced to concrete Cauchy constants for the SAME literal
-- normalized interaction factor; no unspecified O(g) constant remains after
-- those estimates are produced.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational.Base as ℚ using
  (ℚ; 0ℚ; _+_; _-_; _*_; _≤_; _<_; ∣_∣; NonNegative; Positive)
import Data.Rational.Properties as ℚP
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using (cong; subst; sym; trans)

import DASHI.Physics.YangMills.BalabanClayT4PositiveDenominatorQuotientEndpointsExact as Quot

mulNN : ∀ {x y} → 0ℚ ≤ x → 0ℚ ≤ y → 0ℚ ≤ x * y
mulNN {x} {y} xNN yNN =
  let
    instance
      xNonnegative : NonNegative x
      xNonnegative = ℚ.nonNegative xNN
      yNonnegative : NonNegative y
      yNonnegative = ℚ.nonNegative yNN
  in
  ℚP.nonNegative⁻¹ (x * y)

scaleLeft : ∀ {c x y} → 0ℚ ≤ c → x ≤ y → c * x ≤ c * y
scaleLeft {c} cNN xy =
  let instance cNonnegative : NonNegative c; cNonnegative = ℚ.nonNegative cNN
  in ℚP.*-monoˡ-≤-nonNeg c xy

scaleRight : ∀ {c x y} → 0ℚ ≤ c → x ≤ y → x * c ≤ y * c
scaleRight {c} cNN xy =
  let instance cNonnegative : NonNegative c; cNonnegative = ℚ.nonNegative cNN
  in ℚP.*-monoʳ-≤-nonNeg c xy

record InteractionCauchyData : Set where
  field
    Z Z1 Z2 coupling : ℚ
    zLower zUpper firstConstant secondConstant couplingCap : ℚ

    zLowerPositive : 0ℚ < zLower
    ZNonnegative : 0ℚ ≤ Z
    zLowerBelowZ : zLower ≤ Z
    ZBelowUpper : Z ≤ zUpper

    firstConstantNN : 0ℚ ≤ firstConstant
    secondConstantNN : 0ℚ ≤ secondConstant
    couplingNN : 0ℚ ≤ coupling
    couplingCapNN : 0ℚ ≤ couplingCap
    couplingBelowCap : coupling ≤ couplingCap

    firstDerivativeBound : ∣ Z1 ∣ ≤ firstConstant * coupling
    secondDerivativeBound : ∣ Z2 ∣ ≤ secondConstant * coupling

open InteractionCauchyData public

logHessianNumerator : InteractionCauchyData → ℚ
logHessianNumerator d = Z d * Z2 d - Z1 d * Z1 d

numeratorCoefficient : InteractionCauchyData → ℚ
numeratorCoefficient d =
  zUpper d * secondConstant d
    + (firstConstant d * firstConstant d) * couplingCap d

numeratorCoefficientNN :
  (d : InteractionCauchyData) → 0ℚ ≤ numeratorCoefficient d
numeratorCoefficientNN d =
  ℚP.+-mono-≤
    (mulNN (ℚP.≤-trans (ZNonnegative d) (ZBelowUpper d))
      (secondConstantNN d))
    (mulNN
      (mulNN (firstConstantNN d) (firstConstantNN d))
      (couplingCapNN d))

absoluteNumeratorTriangle :
  (d : InteractionCauchyData) →
  ∣ logHessianNumerator d ∣
  ≤ Z d * ∣ Z2 d ∣ + ∣ Z1 d ∣ * ∣ Z1 d ∣
absoluteNumeratorTriangle d =
  let
    differenceAsSum :
      Z d * Z2 d - Z1 d * Z1 d
      ≡ Z d * Z2 d + (- (Z1 d * Z1 d))
    differenceAsSum = ℚRing.solve-∀ (Z d) (Z1 d) (Z2 d)

    triangle = ℚP.∣p+q∣≤∣p∣+∣q∣
      (Z d * Z2 d) (- (Z1 d * Z1 d))

    zAbs : ∣ Z d ∣ ≡ Z d
    zAbs = ℚP.0≤p⇒∣p∣≡p (ZNonnegative d)

    firstProduct : ∣ Z d * Z2 d ∣ ≡ Z d * ∣ Z2 d ∣
    firstProduct =
      trans (ℚP.∣p*q∣≡∣p∣*∣q∣ (Z d) (Z2 d))
        (cong (_* ∣ Z2 d ∣) zAbs)

    squareAbs : ∣ Z1 d * Z1 d ∣ ≡ ∣ Z1 d ∣ * ∣ Z1 d ∣
    squareAbs = ℚP.∣p*q∣≡∣p∣*∣q∣ (Z1 d) (Z1 d)

    negSquareAbs : ∣ - (Z1 d * Z1 d) ∣ ≡ ∣ Z1 d ∣ * ∣ Z1 d ∣
    negSquareAbs = trans (ℚP.∣-p∣≡∣p∣ (Z1 d * Z1 d)) squareAbs
  in
  subst
    (λ left → left ≤ Z d * ∣ Z2 d ∣ + ∣ Z1 d ∣ * ∣ Z1 d ∣)
    (sym (cong ∣_∣ differenceAsSum))
    (subst
      (λ left → left ≤ Z d * ∣ Z2 d ∣ + ∣ Z1 d ∣ * ∣ Z1 d ∣)
      (cong₂ _+_ firstProduct negSquareAbs)
      triangle)
  where
    cong₂ : ∀ {A B C : Set} (f : A → B → C) {a a' : A} {b b' : B} →
      a ≡ a' → b ≡ b' → f a b ≡ f a' b'
    cong₂ f refl refl = refl

absoluteNumeratorBound :
  (d : InteractionCauchyData) →
  ∣ logHessianNumerator d ∣ ≤ numeratorCoefficient d * coupling d
absoluteNumeratorBound d =
  let
    absZ2NN : 0ℚ ≤ ∣ Z2 d ∣
    absZ2NN = ℚP.0≤∣p∣ (Z2 d)

    upperNN : 0ℚ ≤ zUpper d
    upperNN = ℚP.≤-trans (ZNonnegative d) (ZBelowUpper d)

    firstTerm1 : Z d * ∣ Z2 d ∣ ≤ zUpper d * ∣ Z2 d ∣
    firstTerm1 = scaleRight absZ2NN (ZBelowUpper d)

    firstTerm2 : zUpper d * ∣ Z2 d ∣
      ≤ zUpper d * (secondConstant d * coupling d)
    firstTerm2 = scaleLeft upperNN (secondDerivativeBound d)

    absZ1NN : 0ℚ ≤ ∣ Z1 d ∣
    absZ1NN = ℚP.0≤∣p∣ (Z1 d)

    firstMajorantNN : 0ℚ ≤ firstConstant d * coupling d
    firstMajorantNN = mulNN (firstConstantNN d) (couplingNN d)

    squareBound :
      ∣ Z1 d ∣ * ∣ Z1 d ∣
      ≤ (firstConstant d * coupling d) * (firstConstant d * coupling d)
    squareBound =
      ℚP.≤-trans
        (scaleLeft absZ1NN (firstDerivativeBound d))
        (scaleRight firstMajorantNN (firstDerivativeBound d))

    couplingSquareBelow : coupling d * coupling d ≤ couplingCap d * coupling d
    couplingSquareBelow = scaleRight (couplingNN d) (couplingBelowCap d)

    squareToLinear :
      (firstConstant d * coupling d) * (firstConstant d * coupling d)
      ≤ ((firstConstant d * firstConstant d) * couplingCap d) * coupling d
    squareToLinear =
      subst
        (λ left → left ≤ ((firstConstant d * firstConstant d) * couplingCap d) * coupling d)
        (ℚRing.solve-∀ (firstConstant d) (coupling d))
        (subst
          (λ right →
            (firstConstant d * firstConstant d) * (coupling d * coupling d) ≤ right)
          (ℚRing.solve-∀ (firstConstant d) (couplingCap d) (coupling d))
          (scaleLeft
            (mulNN (firstConstantNN d) (firstConstantNN d))
            couplingSquareBelow))

    summed = ℚP.+-mono-≤
      (ℚP.≤-trans firstTerm1 firstTerm2)
      (ℚP.≤-trans squareBound squareToLinear)

    targetShape :
      zUpper d * (secondConstant d * coupling d)
        + ((firstConstant d * firstConstant d) * couplingCap d) * coupling d
      ≡ numeratorCoefficient d * coupling d
    targetShape = ℚRing.solve-∀
      (zUpper d) (secondConstant d) (firstConstant d)
      (couplingCap d) (coupling d)
  in
  ℚP.≤-trans (absoluteNumeratorTriangle d)
    (subst
      (λ right →
        Z d * ∣ Z2 d ∣ + ∣ Z1 d ∣ * ∣ Z1 d ∣ ≤ right)
      targetShape
      summed)

zLowerSquaredPositive :
  (d : InteractionCauchyData) → 0ℚ < zLower d * zLower d
zLowerSquaredPositive d =
  let instance zPos : Positive (zLower d); zPos = ℚ.positive (zLowerPositive d)
  in ℚP.positive⁻¹ (zLower d * zLower d)

zSquaredPositive :
  (d : InteractionCauchyData) → 0ℚ < Z d * Z d
zSquaredPositive d =
  let
    zPositive : 0ℚ < Z d
    zPositive = ℚP.<-≤-trans (zLowerPositive d) (zLowerBelowZ d)
    instance zPos : Positive (Z d)
    zPos = ℚ.positive zPositive
  in
  ℚP.positive⁻¹ (Z d * Z d)

zLowerSquaredBelowZSquared :
  (d : InteractionCauchyData) → zLower d * zLower d ≤ Z d * Z d
zLowerSquaredBelowZSquared d =
  let
    lowerNN = ℚP.<⇒≤ (zLowerPositive d)
    zNN = ZNonnegative d
    first = scaleLeft lowerNN (zLowerBelowZ d)
    second = scaleRight zNN (zLowerBelowZ d)
  in
  ℚP.≤-trans first second

interactionConstant : InteractionCauchyData → ℚ
interactionConstant d =
  Quot.dividePositive
    (numeratorCoefficient d)
    (zLower d * zLower d)
    (zLowerSquaredPositive d)

logHessianQuotientBound :
  (d : InteractionCauchyData) →
  Quot.dividePositive
      ∣ logHessianNumerator d ∣
      (Z d * Z d)
      (zSquaredPositive d)
  ≤ interactionConstant d * coupling d
logHessianQuotientBound d =
  let
    numeratorNN : 0ℚ ≤ numeratorCoefficient d * coupling d
    numeratorNN = mulNN (numeratorCoefficientNN d) (couplingNN d)

    numeratorStep =
      Quot.dividePositiveNumeratorMonotone
        ∣ logHessianNumerator d ∣
        (numeratorCoefficient d * coupling d)
        (Z d * Z d)
        (zSquaredPositive d)
        (absoluteNumeratorBound d)

    denominatorStep =
      Quot.dividePositiveDenominatorAntitoneNonnegative
        (numeratorCoefficient d * coupling d)
        (zLower d * zLower d)
        (Z d * Z d)
        numeratorNN
        (zLowerSquaredPositive d)
        (zSquaredPositive d)
        (zLowerSquaredBelowZSquared d)

    factorExact :
      Quot.dividePositive
        (numeratorCoefficient d * coupling d)
        (zLower d * zLower d)
        (zLowerSquaredPositive d)
      ≡ interactionConstant d * coupling d
    factorExact = ℚRing.solve-∀
      (numeratorCoefficient d)
      (coupling d)
      (Quot.positiveReciprocal
        (zLower d * zLower d) (zLowerSquaredPositive d))
  in
  ℚP.≤-trans numeratorStep
    (subst
      (λ right →
        Quot.dividePositive
          (numeratorCoefficient d * coupling d)
          (Z d * Z d)
          (zSquaredPositive d)
        ≤ right)
      factorExact
      denominatorStep)
