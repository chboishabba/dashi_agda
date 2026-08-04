module DASHI.Physics.YangMills.BalabanP33BishopTaylorPolynomialFormExact where

------------------------------------------------------------------------
-- PRIMARY SOURCE
--
-- Zachary Murray,
-- "Constructive Analysis in the Agda Proof Assistant",
-- B.Sc. Honours thesis, Dalhousie University, 2022.
-- arXiv:2205.08354. No DOI assigned.
--
-- DASHI CONTRIBUTION
--
-- Normalize the first two concrete Bishop sine/cosine magnitudes to the
-- literal low-order polynomials.  Combined with the alternating interlacing
-- theorem this proves, on the nonnegative half ball,
--
--   x - x^3/6 <= sin x <= x,
--   1 - x^2/2 <= cos x <= 1.
--
-- Consequently
--
--   0 <= x - sin x <= x^3/6,
--   0 <= 1 - cos x <= x^2/2.
--
-- All coefficients are the concrete factorial rationals from the existing
-- Bishop series; no real-analysis estimate is supplied as a field.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (zero; suc)
open import Data.Integer.Base using (+_)
open import Data.Rational.Unnormalised as ℚ using (ℚᵘ; _/_; 0ℚᵘ)
import Data.Rational.Unnormalised.Properties as ℚP

import Real as BishopReal
import RealProperties as BishopProperties

import DASHI.Foundations.BishopPowerSeriesElementaryBridgeExact as Elementary
import DASHI.Physics.YangMills.BalabanBishopConcreteSineCosineInterlacingExact as Concrete
import DASHI.Physics.YangMills.BalabanBishopFactorialPowerRecurrenceExact as Recurrence
import DASHI.Physics.YangMills.BalabanP33BishopLowOrderTaylorBracketsExact as Taylor
open import DASHI.Physics.YangMills.CompactLieProofLevel

oneSixth oneHalf : ℚᵘ
oneSixth = + 1 / 6
oneHalf = + 1 / 2

bishopOneSixth bishopOneHalf : BishopReal.ℝ
bishopOneSixth = BishopReal._⋆ oneSixth
bishopOneHalf = BishopReal._⋆ oneHalf

square cube : BishopReal.ℝ → BishopReal.ℝ
square value = BishopReal._*_ value value
cube value = BishopReal._*_ (square value) value

sineCubicTerm : BishopReal.ℝ → BishopReal.ℝ
sineCubicTerm value = BishopReal._*_ bishopOneSixth (cube value)

cosineQuadraticTerm : BishopReal.ℝ → BishopReal.ℝ
cosineQuadraticTerm value = BishopReal._*_ bishopOneHalf (square value)

powerAbsoluteEquivalentPower :
  ∀ value exponent →
  BishopReal.NonNegative value →
  BishopReal._≃_
    (BishopReal.∣_∣ (Recurrence.pow value exponent))
    (Recurrence.pow value exponent)
powerAbsoluteEquivalentPower value exponent valueNonnegative =
  BishopProperties.nonNegx⇒∣x∣≃x
    (Recurrence.powerNonnegative value exponent valueNonnegative)

sineMagnitudeZeroEquivalentValue :
  ∀ value →
  BishopReal.NonNegative value →
  BishopReal._≃_
    (Recurrence.sineMagnitudeTerm value zero)
    value
sineMagnitudeZeroEquivalentValue value valueNonnegative =
  BishopProperties.≃-trans
    (BishopProperties.*-cong
      (BishopProperties.⋆-cong ℚP.≃-refl)
      (powerAbsoluteEquivalentPower value (suc zero) valueNonnegative))
    (let open BishopProperties.ℝ-Solver
     in solve 1
        (λ x → Κ (+ 1 / 1) ⊗ (Κ (+ 1 / 1) ⊗ x) ⊜ x)
        BishopProperties.≃-refl value)

sineMagnitudeOneEquivalentCubic :
  ∀ value →
  BishopReal.NonNegative value →
  BishopReal._≃_
    (Recurrence.sineMagnitudeTerm value (suc zero))
    (sineCubicTerm value)
sineMagnitudeOneEquivalentCubic value valueNonnegative =
  BishopProperties.≃-trans
    (BishopProperties.*-cong
      (BishopProperties.⋆-cong ℚP.≃-refl)
      (powerAbsoluteEquivalentPower value
        (suc (suc (suc zero))) valueNonnegative))
    (let open BishopProperties.ℝ-Solver
     in solve 1
        (λ x →
          Κ oneSixth ⊗ (((Κ (+ 1 / 1) ⊗ x) ⊗ x) ⊗ x)
          ⊜ Κ oneSixth ⊗ ((x ⊗ x) ⊗ x))
        BishopProperties.≃-refl value)

cosineMagnitudeZeroEquivalentOne :
  ∀ value →
  BishopReal.NonNegative value →
  BishopReal._≃_
    (Recurrence.cosineMagnitudeTerm value zero)
    BishopReal.1ℝ
cosineMagnitudeZeroEquivalentOne value valueNonnegative =
  BishopProperties.≃-trans
    (BishopProperties.*-cong
      (BishopProperties.⋆-cong ℚP.≃-refl)
      (powerAbsoluteEquivalentPower value zero valueNonnegative))
    (let open BishopProperties.ℝ-Solver
     in solve 0
        (Κ (+ 1 / 1) ⊗ Κ (+ 1 / 1) ⊜ Κ (+ 1 / 1))
        BishopProperties.≃-refl)

cosineMagnitudeOneEquivalentQuadratic :
  ∀ value →
  BishopReal.NonNegative value →
  BishopReal._≃_
    (Recurrence.cosineMagnitudeTerm value (suc zero))
    (cosineQuadraticTerm value)
cosineMagnitudeOneEquivalentQuadratic value valueNonnegative =
  BishopProperties.≃-trans
    (BishopProperties.*-cong
      (BishopProperties.⋆-cong ℚP.≃-refl)
      (powerAbsoluteEquivalentPower value
        (suc (suc zero)) valueNonnegative))
    (let open BishopProperties.ℝ-Solver
     in solve 1
        (λ x →
          Κ oneHalf ⊗ ((Κ (+ 1 / 1) ⊗ x) ⊗ x)
          ⊜ Κ oneHalf ⊗ (x ⊗ x))
        BishopProperties.≃-refl value)

record PolynomialTaylorBounds
    (dataSet : Elementary.BishopElementaryPowerSeriesData)
    (value : BishopReal.ℝ) : Set₁ where
  field
    sineCubicLower :
      BishopReal._≤_
        (BishopReal._-_ value (sineCubicTerm value))
        (Elementary.bishopSin dataSet value)

    sineLinearUpper :
      BishopReal._≤_ (Elementary.bishopSin dataSet value) value

    cosineQuadraticLower :
      BishopReal._≤_
        (BishopReal._-_ BishopReal.1ℝ (cosineQuadraticTerm value))
        (Elementary.bishopCos dataSet value)

    cosineOneUpper :
      BishopReal._≤_ (Elementary.bishopCos dataSet value) BishopReal.1ℝ

open PolynomialTaylorBounds public

polynomialTaylorBounds :
  ∀ {dataSet value} →
  Concrete.ConcreteHalfBallSeriesInputs dataSet value →
  PolynomialTaylorBounds dataSet value
polynomialTaylorBounds {value = value} inputs =
  let
    brackets = Taylor.lowOrderTaylorBrackets inputs
    valueNonnegative = Concrete.valueNonnegative inputs
    sineZero = sineMagnitudeZeroEquivalentValue value valueNonnegative
    sineOne = sineMagnitudeOneEquivalentCubic value valueNonnegative
    cosineZero = cosineMagnitudeZeroEquivalentOne value valueNonnegative
    cosineOne = cosineMagnitudeOneEquivalentQuadratic value valueNonnegative
  in
  record
    { sineCubicLower =
        BishopProperties.≤-respˡ-≃
          (BishopProperties.≃-symm
            (BishopProperties.+-cong sineZero
              (BishopProperties.-‿cong sineOne)))
          (Taylor.sineLower brackets)
    ; sineLinearUpper =
        BishopProperties.≤-respʳ-≃ sineZero
          (Taylor.sineUpper brackets)
    ; cosineQuadraticLower =
        BishopProperties.≤-respˡ-≃
          (BishopProperties.≃-symm
            (BishopProperties.+-cong cosineZero
              (BishopProperties.-‿cong cosineOne)))
          (Taylor.cosineLower brackets)
    ; cosineOneUpper =
        BishopProperties.≤-respʳ-≃ cosineZero
          (Taylor.cosineUpper brackets)
    }

orderGivesNonnegativeDifference :
  ∀ {left right} →
  BishopReal._≤_ left right →
  BishopReal._≤_ BishopReal.0ℝ (BishopReal._-_ right left)
orderGivesNonnegativeDifference {left} {right} leftBelowRight =
  BishopProperties.≤-respˡ-≃
    (let open BishopProperties.ℝ-Solver
     in solve 1
        (λ x → Κ 0ℚᵘ ⊜ x ⊖ x)
        BishopProperties.≃-refl left)
    (BishopProperties.+-monoˡ-≤
      (BishopReal.- left) leftBelowRight)

lowerTaylorGivesDefectUpper :
  ∀ {center error value} →
  BishopReal._≤_ (BishopReal._-_ center error) value →
  BishopReal._≤_ (BishopReal._-_ center value) error
lowerTaylorGivesDefectUpper {center} {error} {value} lowerBound =
  BishopProperties.≤-respʳ-≃
    (let open BishopProperties.ℝ-Solver
     in solve 2
        (λ center error →
          center ⊕ (⊝ (center ⊖ error)) ⊜ error)
        BishopProperties.≃-refl center error)
    (BishopProperties.+-monoʳ-≤ center
      (BishopProperties.neg-mono-≤ lowerBound))

record DefectTaylorBounds
    (dataSet : Elementary.BishopElementaryPowerSeriesData)
    (value : BishopReal.ℝ) : Set₁ where
  field
    sineDefectNonnegative :
      BishopReal._≤_ BishopReal.0ℝ
        (BishopReal._-_ value (Elementary.bishopSin dataSet value))

    sineDefectBelowCubic :
      BishopReal._≤_
        (BishopReal._-_ value (Elementary.bishopSin dataSet value))
        (sineCubicTerm value)

    cosineDefectNonnegative :
      BishopReal._≤_ BishopReal.0ℝ
        (BishopReal._-_ BishopReal.1ℝ
          (Elementary.bishopCos dataSet value))

    cosineDefectBelowQuadratic :
      BishopReal._≤_
        (BishopReal._-_ BishopReal.1ℝ
          (Elementary.bishopCos dataSet value))
        (cosineQuadraticTerm value)

open DefectTaylorBounds public

defectTaylorBounds :
  ∀ {dataSet value} →
  Concrete.ConcreteHalfBallSeriesInputs dataSet value →
  DefectTaylorBounds dataSet value
defectTaylorBounds inputs =
  let bounds = polynomialTaylorBounds inputs
  in record
    { sineDefectNonnegative =
        orderGivesNonnegativeDifference (sineLinearUpper bounds)
    ; sineDefectBelowCubic =
        lowerTaylorGivesDefectUpper (sineCubicLower bounds)
    ; cosineDefectNonnegative =
        orderGivesNonnegativeDifference (cosineOneUpper bounds)
    ; cosineDefectBelowQuadratic =
        lowerTaylorGivesDefectUpper (cosineQuadraticLower bounds)
    }

p33BishopPolynomialTaylorLevel : ProofLevel
p33BishopPolynomialTaylorLevel = machineChecked

p33BishopSineCosineDefectLevel : ProofLevel
p33BishopSineCosineDefectLevel = machineChecked
