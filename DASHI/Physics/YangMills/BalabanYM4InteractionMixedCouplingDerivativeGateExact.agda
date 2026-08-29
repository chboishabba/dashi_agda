{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanYM4InteractionMixedCouplingDerivativeGateExact where

------------------------------------------------------------------------
-- ROW A: THE SAME NORMALIZED INTERACTION PACKAGE ALSO PRODUCES A3's L_int
--
-- PRIMARY SOURCE
--
-- Tadeusz Bałaban,
-- "Renormalization Group Approach to Lattice Gauge Field Theories. I.",
-- Communications in Mathematical Physics 109 (1987), 249--301.
-- DOI: 10.1007/BF01215223.
--
-- Let Z be the normalized nonlinear interaction factor, Z1 and Z2 its first
-- and second background derivatives, and let
--
--   G0 = d_g Z,   G1 = d_g Z1,   G2 = d_g Z2.
--
-- With N = Z Z2 - Z1^2,
--
--   beta_int = N / Z^2,
--   d_g N = G0 Z2 + Z G2 - 2 Z1 G1,
--   d_g beta_int = ((d_g N) Z - 2 N G0) / Z^3.
--
-- The companion log-Hessian module already proves
--
--   |N| <= M g,   M = z1 B + A^2 gamma.
--
-- If |G0|<=D0, |G1|<=D1, |G2|<=D2, this module proves the explicit cutoff-
-- independent coupling derivative bound
--
--   |d_g beta_int| <= L_int,
--
--   ND = z1 D2 + (D0 B + 2 A D1) gamma,
--   L_int = [ z1 ND + 2 M gamma D0 ] / z0^3.
--
-- Thus A2 and the interaction part of A3 are fed by one literal mixed-Cauchy
-- package rather than unrelated estimates.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational.Base as ℚ using
  (ℚ; 0ℚ; _+_; _-_; _*_; _≤_; _<_; ∣_∣; NonNegative; Positive)
import Data.Rational.Properties as ℚP
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using (cong; cong₂; subst; sym; trans)

import DASHI.Physics.YangMills.BalabanClayT4PositiveDenominatorQuotientEndpointsExact as Quot
import DASHI.Physics.YangMills.BalabanYM4InteractionLogHessianCauchyGateExact as H

open H using
  ( InteractionCauchyData; Z; Z1; Z2; coupling; zLower; zUpper
  ; firstConstant; secondConstant; couplingCap
  ; ZNonnegative; ZBelowUpper; couplingNN; couplingBelowCap
  ; firstConstantNN; secondConstantNN
  ; firstDerivativeBound; secondDerivativeBound
  ; zLowerPositive; zLowerBelowZ
  ; logHessianNumerator; numeratorCoefficient; numeratorCoefficientNN
  ; absoluteNumeratorBound; mulNN; scaleLeft; scaleRight )

two : ℚ
two = (+ 1 / 1) + (+ 1 / 1)

record MixedInteractionCauchyData : Set where
  field
    base : InteractionCauchyData
    G0 G1 G2 : ℚ
    D0 D1 D2 : ℚ
    D0NN : 0ℚ ≤ D0
    D1NN : 0ℚ ≤ D1
    D2NN : 0ℚ ≤ D2
    G0Bound : ∣ G0 ∣ ≤ D0
    G1Bound : ∣ G1 ∣ ≤ D1
    G2Bound : ∣ G2 ∣ ≤ D2

open MixedInteractionCauchyData public

numeratorDerivative : MixedInteractionCauchyData → ℚ
numeratorDerivative d =
  G0 d * Z (base d)
    * 0ℚ
  + (G0 d * Z2 (base d) + Z (base d) * G2 d - two * Z1 (base d) * G1 d)

-- Definitional zero term above keeps the polynomial shape explicit for the
-- ring solver while reducing to the expected formula.
numeratorDerivativeExpected :
  ∀ d → numeratorDerivative d
    ≡ G0 d * Z2 (base d) + Z (base d) * G2 d - two * Z1 (base d) * G1 d
numeratorDerivativeExpected d = ℚRing.solve-∀
  (G0 d) (Z (base d)) (Z2 (base d)) (G2 d) (Z1 (base d)) (G1 d)

numeratorDerivativeConstant : MixedInteractionCauchyData → ℚ
numeratorDerivativeConstant d =
  zUpper (base d) * D2 d
    + (D0 d * secondConstant (base d)
       + two * firstConstant (base d) * D1 d) * couplingCap (base d)

numeratorDerivativeConstantNN :
  (d : MixedInteractionCauchyData) → 0ℚ ≤ numeratorDerivativeConstant d
numeratorDerivativeConstantNN d =
  let
    b = base d
    zUpperNN : 0ℚ ≤ zUpper b
    zUpperNN = ℚP.≤-trans (ZNonnegative b) (ZBelowUpper b)
    twoNN : 0ℚ ≤ two
    twoNN = ℚP.nonNegative⁻¹ two
    slopeNN = ℚP.+-mono-≤
      (mulNN (D0NN d) (secondConstantNN b))
      (mulNN (mulNN twoNN (firstConstantNN b)) (D1NN d))
  in
  ℚP.+-mono-≤
    (mulNN zUpperNN (D2NN d))
    (mulNN slopeNN (H.couplingCapNN b))

absoluteNumeratorDerivativeBound :
  (d : MixedInteractionCauchyData) →
  ∣ numeratorDerivative d ∣ ≤ numeratorDerivativeConstant d
absoluteNumeratorDerivativeBound d =
  let
    b = base d
    zUpperNN : 0ℚ ≤ zUpper b
    zUpperNN = ℚP.≤-trans (ZNonnegative b) (ZBelowUpper b)
    absG0NN = ℚP.0≤∣p∣ (G0 d)
    absG1NN = ℚP.0≤∣p∣ (G1 d)
    absG2NN = ℚP.0≤∣p∣ (G2 d)
    absZ1NN = ℚP.0≤∣p∣ (Z1 b)
    absZ2NN = ℚP.0≤∣p∣ (Z2 b)
    twoNN : 0ℚ ≤ two
    twoNN = ℚP.nonNegative⁻¹ two

    firstTerm : ∣ G0 d * Z2 b ∣ ≤ (D0 d * secondConstant b) * coupling b
    firstTerm =
      subst
        (λ left → left ≤ (D0 d * secondConstant b) * coupling b)
        (ℚP.∣p*q∣≡∣p∣*∣q∣ (G0 d) (Z2 b))
        (ℚP.≤-trans
          (scaleRight absZ2NN (G0Bound d))
          (subst
            (λ right → D0 d * ∣ Z2 b ∣ ≤ right)
            (ℚRing.solve-∀ (D0 d) (secondConstant b) (coupling b))
            (scaleLeft (D0NN d) (secondDerivativeBound b))))

    secondTerm : ∣ Z b * G2 d ∣ ≤ zUpper b * D2 d
    secondTerm =
      subst
        (λ left → left ≤ zUpper b * D2 d)
        (trans
          (ℚP.∣p*q∣≡∣p∣*∣q∣ (Z b) (G2 d))
          (cong (_* ∣ G2 d ∣) (ℚP.0≤p⇒∣p∣≡p (ZNonnegative b))))
        (ℚP.≤-trans
          (scaleRight absG2NN (ZBelowUpper b))
          (scaleLeft zUpperNN (G2Bound d)))

    thirdTerm :
      ∣ two * Z1 b * G1 d ∣
      ≤ (two * firstConstant b * D1 d) * coupling b
    thirdTerm =
      subst
        (λ left → left ≤ (two * firstConstant b * D1 d) * coupling b)
        (trans
          (ℚP.∣p*q∣≡∣p∣*∣q∣ (two * Z1 b) (G1 d))
          (cong (_* ∣ G1 d ∣)
            (trans
              (ℚP.∣p*q∣≡∣p∣*∣q∣ two (Z1 b))
              (cong (_* ∣ Z1 b ∣) (ℚP.0≤p⇒∣p∣≡p twoNN)))))
        (ℚP.≤-trans
          (scaleRight absG1NN
            (scaleLeft twoNN (firstDerivativeBound b)))
          (subst
            (λ right → (two * (firstConstant b * coupling b)) * ∣ G1 d ∣ ≤ right)
            (ℚRing.solve-∀ two (firstConstant b) (D1 d) (coupling b))
            (scaleLeft
              (mulNN twoNN (mulNN (firstConstantNN b) (couplingNN b)))
              (G1Bound d))))

    expressionTriangle :
      ∣ G0 d * Z2 b + Z b * G2 d - two * Z1 b * G1 d ∣
      ≤ ∣ G0 d * Z2 b ∣ + ∣ Z b * G2 d ∣ + ∣ two * Z1 b * G1 d ∣
    expressionTriangle =
      let
        split :
          G0 d * Z2 b + Z b * G2 d - two * Z1 b * G1 d
          ≡ (G0 d * Z2 b + Z b * G2 d) + (- (two * Z1 b * G1 d))
        split = ℚRing.solve-∀ (G0 d) (Z2 b) (Z b) (G2 d) two (Z1 b) (G1 d)

        outer = ℚP.∣p+q∣≤∣p∣+∣q∣
          (G0 d * Z2 b + Z b * G2 d) (- (two * Z1 b * G1 d))
        inner = ℚP.∣p+q∣≤∣p∣+∣q∣ (G0 d * Z2 b) (Z b * G2 d)
      in
      subst
        (λ left → left ≤ ∣ G0 d * Z2 b ∣ + ∣ Z b * G2 d ∣ + ∣ two * Z1 b * G1 d ∣)
        (sym (cong ∣_∣ split))
        (ℚP.≤-trans outer
          (ℚP.+-mono-≤ inner
            (subst
              (λ q → q ≤ ∣ two * Z1 b * G1 d ∣)
              (ℚP.∣-p∣≡∣p∣ (two * Z1 b * G1 d))
              ℚP.≤-refl)))

    summed = ℚP.+-mono-≤
      (ℚP.+-mono-≤ firstTerm secondTerm)
      thirdTerm

    slopeToCap :
      (D0 d * secondConstant b) * coupling b
        + (two * firstConstant b * D1 d) * coupling b
      ≤ (D0 d * secondConstant b + two * firstConstant b * D1 d)
          * couplingCap b
    slopeToCap =
      subst
        (λ left → left ≤
          (D0 d * secondConstant b + two * firstConstant b * D1 d)
            * couplingCap b)
        (ℚRing.solve-∀
          (D0 d) (secondConstant b) two (firstConstant b) (D1 d) (coupling b))
        (scaleLeft
          (ℚP.+-mono-≤
            (mulNN (D0NN d) (secondConstantNN b))
            (mulNN (mulNN twoNN (firstConstantNN b)) (D1NN d)))
          (couplingBelowCap b))

    finalShape :
      zUpper b * D2 d
      + (D0 d * secondConstant b + two * firstConstant b * D1 d) * couplingCap b
      ≡ numeratorDerivativeConstant d
    finalShape = refl
  in
  subst
    (λ left → left ≤ numeratorDerivativeConstant d)
    (cong ∣_∣ (numeratorDerivativeExpected d))
    (ℚP.≤-trans expressionTriangle
      (ℚP.≤-trans summed
        (subst
          (λ right →
            (D0 d * secondConstant b) * coupling b
              + zUpper b * D2 d
              + (two * firstConstant b * D1 d) * coupling b ≤ right)
          (sym finalShape)
          (subst
            (λ left → left ≤ zUpper b * D2 d
              + (D0 d * secondConstant b + two * firstConstant b * D1 d)
                  * couplingCap b)
            (ℚRing.solve-∀
              (D0 d) (secondConstant b) (coupling b)
              (zUpper b) (D2 d) two (firstConstant b) (D1 d))
            (ℚP.+-mono-≤ ℚP.≤-refl slopeToCap)))))

betaDerivativeNumerator : MixedInteractionCauchyData → ℚ
betaDerivativeNumerator d =
  numeratorDerivative d * Z (base d)
    - two * logHessianNumerator (base d) * G0 d

betaDerivativeNumeratorConstant : MixedInteractionCauchyData → ℚ
betaDerivativeNumeratorConstant d =
  zUpper (base d) * numeratorDerivativeConstant d
    + two * numeratorCoefficient (base d) * couplingCap (base d) * D0 d

betaDerivativeNumeratorConstantNN :
  (d : MixedInteractionCauchyData) → 0ℚ ≤ betaDerivativeNumeratorConstant d
betaDerivativeNumeratorConstantNN d =
  let
    b = base d
    zUpperNN = ℚP.≤-trans (ZNonnegative b) (ZBelowUpper b)
    twoNN : 0ℚ ≤ two
    twoNN = ℚP.nonNegative⁻¹ two
  in
  ℚP.+-mono-≤
    (mulNN zUpperNN (numeratorDerivativeConstantNN d))
    (mulNN
      (mulNN
        (mulNN twoNN (numeratorCoefficientNN b))
        (H.couplingCapNN b))
      (D0NN d))

absoluteBetaDerivativeNumeratorBound :
  (d : MixedInteractionCauchyData) →
  ∣ betaDerivativeNumerator d ∣ ≤ betaDerivativeNumeratorConstant d
absoluteBetaDerivativeNumeratorBound d =
  let
    b = base d
    zUpperNN = ℚP.≤-trans (ZNonnegative b) (ZBelowUpper b)
    absZNN = ℚP.0≤∣p∣ (Z b)
    absG0NN = ℚP.0≤∣p∣ (G0 d)
    twoNN : 0ℚ ≤ two
    twoNN = ℚP.nonNegative⁻¹ two

    firstTerm :
      ∣ numeratorDerivative d * Z b ∣
      ≤ zUpper b * numeratorDerivativeConstant d
    firstTerm =
      subst
        (λ left → left ≤ zUpper b * numeratorDerivativeConstant d)
        (ℚP.∣p*q∣≡∣p∣*∣q∣ (numeratorDerivative d) (Z b))
        (ℚP.≤-trans
          (scaleRight absZNN (absoluteNumeratorDerivativeBound d))
          (subst
            (λ right → numeratorDerivativeConstant d * ∣ Z b ∣ ≤ right)
            (ℚP.*-comm (zUpper b) (numeratorDerivativeConstant d))
            (scaleLeft (numeratorDerivativeConstantNN d)
              (subst (λ z → z ≤ zUpper b)
                (ℚP.0≤p⇒∣p∣≡p (ZNonnegative b)) (ZBelowUpper b)))))

    secondTerm :
      ∣ two * logHessianNumerator b * G0 d ∣
      ≤ two * numeratorCoefficient b * couplingCap b * D0 d
    secondTerm =
      subst
        (λ left → left ≤ two * numeratorCoefficient b * couplingCap b * D0 d)
        (trans
          (ℚP.∣p*q∣≡∣p∣*∣q∣ (two * logHessianNumerator b) (G0 d))
          (cong (_* ∣ G0 d ∣)
            (trans
              (ℚP.∣p*q∣≡∣p∣*∣q∣ two (logHessianNumerator b))
              (cong (_* ∣ logHessianNumerator b ∣)
                (ℚP.0≤p⇒∣p∣≡p twoNN)))))
        (let
          nBound = absoluteNumeratorBound b
          nToCap : ∣ logHessianNumerator b ∣ ≤ numeratorCoefficient b * couplingCap b
          nToCap = ℚP.≤-trans nBound
            (scaleLeft (numeratorCoefficientNN b) (couplingBelowCap b))
          firstScaled = scaleLeft twoNN nToCap
          firstScaledNN = mulNN twoNN
            (mulNN (numeratorCoefficientNN b) (H.couplingCapNN b))
         in
          ℚP.≤-trans
            (scaleRight absG0NN firstScaled)
            (scaleLeft firstScaledNN (G0Bound d)))

    triangle =
      let
        split : betaDerivativeNumerator d
          ≡ numeratorDerivative d * Z b + (- (two * logHessianNumerator b * G0 d))
        split = ℚRing.solve-∀
          (numeratorDerivative d) (Z b) two (logHessianNumerator b) (G0 d)
      in
      subst
        (λ left → left ≤
          ∣ numeratorDerivative d * Z b ∣ + ∣ two * logHessianNumerator b * G0 d ∣)
        (sym (cong ∣_∣ split))
        (ℚP.≤-trans
          (ℚP.∣p+q∣≤∣p∣+∣q∣
            (numeratorDerivative d * Z b)
            (- (two * logHessianNumerator b * G0 d)))
          (ℚP.+-mono-≤ ℚP.≤-refl
            (subst
              (λ q → q ≤ ∣ two * logHessianNumerator b * G0 d ∣)
              (ℚP.∣-p∣≡∣p∣ (two * logHessianNumerator b * G0 d))
              ℚP.≤-refl)))
  in
  ℚP.≤-trans triangle (ℚP.+-mono-≤ firstTerm secondTerm)

zLowerCubedPositive :
  (d : MixedInteractionCauchyData) →
  0ℚ < (zLower (base d) * zLower (base d)) * zLower (base d)
zLowerCubedPositive d =
  let
    b = base d
    zPos = zLowerPositive b
    zSqPos = H.zLowerSquaredPositive b
    instance zPositive : Positive (zLower b); zPositive = ℚ.positive zPos
    instance zSqPositive : Positive (zLower b * zLower b); zSqPositive = ℚ.positive zSqPos
  in
  ℚP.positive⁻¹ ((zLower b * zLower b) * zLower b)

zCubedPositive :
  (d : MixedInteractionCauchyData) →
  0ℚ < (Z (base d) * Z (base d)) * Z (base d)
zCubedPositive d =
  let
    b = base d
    zPos = ℚP.<-≤-trans (zLowerPositive b) (zLowerBelowZ b)
    zSqPos = H.zSquaredPositive b
    instance zPositive : Positive (Z b); zPositive = ℚ.positive zPos
    instance zSqPositive : Positive (Z b * Z b); zSqPositive = ℚ.positive zSqPos
  in
  ℚP.positive⁻¹ ((Z b * Z b) * Z b)

zLowerCubedBelowZCubed :
  (d : MixedInteractionCauchyData) →
  (zLower (base d) * zLower (base d)) * zLower (base d)
  ≤ (Z (base d) * Z (base d)) * Z (base d)
zLowerCubedBelowZCubed d =
  let
    b = base d
    zNN = ZNonnegative b
    lowerNN = ℚP.<⇒≤ (zLowerPositive b)
    squares = H.zLowerSquaredBelowZSquared b
  in
  ℚP.≤-trans
    (scaleRight lowerNN squares)
    (scaleLeft (mulNN zNN zNN) (zLowerBelowZ b))

interactionDerivativeConstant : MixedInteractionCauchyData → ℚ
interactionDerivativeConstant d =
  Quot.dividePositive
    (betaDerivativeNumeratorConstant d)
    ((zLower (base d) * zLower (base d)) * zLower (base d))
    (zLowerCubedPositive d)

-- MAIN A3 INTERACTION RESULT.
interactionCouplingDerivativeBound :
  (d : MixedInteractionCauchyData) →
  Quot.dividePositive
    ∣ betaDerivativeNumerator d ∣
    ((Z (base d) * Z (base d)) * Z (base d))
    (zCubedPositive d)
  ≤ interactionDerivativeConstant d
interactionCouplingDerivativeBound d =
  let
    numeratorStep =
      Quot.dividePositiveNumeratorMonotone
        ∣ betaDerivativeNumerator d ∣
        (betaDerivativeNumeratorConstant d)
        ((Z (base d) * Z (base d)) * Z (base d))
        (zCubedPositive d)
        (absoluteBetaDerivativeNumeratorBound d)

    denominatorStep =
      Quot.dividePositiveDenominatorAntitoneNonnegative
        (betaDerivativeNumeratorConstant d)
        ((zLower (base d) * zLower (base d)) * zLower (base d))
        ((Z (base d) * Z (base d)) * Z (base d))
        (betaDerivativeNumeratorConstantNN d)
        (zLowerCubedPositive d)
        (zCubedPositive d)
        (zLowerCubedBelowZCubed d)
  in
  ℚP.≤-trans numeratorStep denominatorStep
