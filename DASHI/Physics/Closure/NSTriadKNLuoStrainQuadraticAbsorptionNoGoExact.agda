module DASHI.Physics.Closure.NSTriadKNLuoStrainQuadraticAbsorptionNoGoExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / AUDIT TARGET
--
-- Ryusho Nemoto,
-- "Global Regularity of the Three-Dimensional Navier-Stokes Equations via
-- a Coupled Energy and Stability Framework".
-- PhilArchive record: NEMGRO.  DOI: none located in the public record.
-- Status: manuscript/preprint.  Its advertised unconditional-absorption
-- mechanism is treated here as an audit target, not as an imported theorem.
--
-- Jeffrey S. Case and Aaron J. Tyrrell,
-- "A Sharp Inequality for Trace-Free Matrices with Applications to
-- Hypersurfaces".
-- DOI: 10.1090/proc/16657.
--
-- DASHI CONTRIBUTION
--
-- Two exact obstructions are checked.
--
-- (1) The quadratic spectral magnitude does not determine cubic strain:
--     spectra (2,-1,-1) and (-2,1,1) both have Q=6, while their cubic
--     traces are +6 and -6.
--
-- (2) No universal nonnegative coefficient K can bound the positive cubic
--     extensional branch by K times the quadratic magnitude.  At scale
--     r=K+1,
--
--       C_3(r) - K Q(r) = 6 (K+1)^2 > 0.
--
-- Thus trace-free spectral rigidity alone cannot produce a scale-free
-- cubic-by-quadratic absorption inequality.  A successful coupled functional
-- must obtain an additional dynamical cancellation or a higher-order term.
------------------------------------------------------------------------

open import Agda.Builtin.List using ([]; _∷_)
open import Data.Rational.Base using
  (ℚ; 0ℚ; 1ℚ; _+_; _*_; -_; _-_; _≤_; _<_; positive; nonNegative)
import Data.Rational.Properties as ℚₚ
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; subst; sym)

import DASHI.Physics.Closure.NSTriadKNLuoStrainSpectralRigidityExact as SR

data StrainOrientation : Set where
  extensional compressive : StrainOrientation

quadraticProjection : StrainOrientation → ℚ
quadraticProjection extensional = SR.quadraticMagnitude 2 (- 1ℚ)
quadraticProjection compressive = SR.quadraticMagnitude (- 2) 1ℚ

cubicProjection : StrainOrientation → ℚ
cubicProjection extensional = SR.cubicTrace 2 (- 1ℚ)
cubicProjection compressive = SR.cubicTrace (- 2) 1ℚ

orientationDistinct : extensional ≢ compressive
orientationDistinct ()

quadraticProjectionCollision :
  quadraticProjection extensional ≡ quadraticProjection compressive
quadraticProjectionCollision = solve []

extensionalQuadraticIsSix : quadraticProjection extensional ≡ 6
extensionalQuadraticIsSix = solve []

compressiveQuadraticIsSix : quadraticProjection compressive ≡ 6
compressiveQuadraticIsSix = solve []

extensionalCubicIsSix : cubicProjection extensional ≡ 6
extensionalCubicIsSix = solve []

compressiveCubicIsMinusSix : cubicProjection compressive ≡ - 6
compressiveCubicIsMinusSix = solve []

cubicOrientationGapIsTwelve :
  cubicProjection extensional - cubicProjection compressive ≡ 12
cubicOrientationGapIsTwelve = solve []

record QuadraticProjectionNonInjective : Set where
  constructor quadraticProjectionNonInjective
  field
    left right : StrainOrientation
    inputsDistinct : left ≢ right
    outputsEqual : quadraticProjection left ≡ quadraticProjection right

quadraticProjectionIsNonInjective : QuadraticProjectionNonInjective
quadraticProjectionIsNonInjective =
  quadraticProjectionNonInjective
    extensional
    compressive
    orientationDistinct
    quadraticProjectionCollision

scaleForCoefficient : ℚ → ℚ
scaleForCoefficient coefficient = coefficient + 1ℚ

quadraticAtAuditScale : ℚ → ℚ
quadraticAtAuditScale coefficient =
  SR.quadraticMagnitude
    (2 * scaleForCoefficient coefficient)
    (- scaleForCoefficient coefficient)

cubicAtAuditScale : ℚ → ℚ
cubicAtAuditScale coefficient =
  SR.cubicTrace
    (2 * scaleForCoefficient coefficient)
    (- scaleForCoefficient coefficient)

absorptionGap : ℚ → ℚ
absorptionGap coefficient =
  cubicAtAuditScale coefficient
  - coefficient * quadraticAtAuditScale coefficient

quadraticAuditScaleClosedForm :
  ∀ coefficient →
  quadraticAtAuditScale coefficient
  ≡ 6 * SR.square (scaleForCoefficient coefficient)
quadraticAuditScaleClosedForm coefficient = solve (coefficient ∷ [])

cubicAuditScaleClosedForm :
  ∀ coefficient →
  cubicAtAuditScale coefficient
  ≡ 6 * SR.cube (scaleForCoefficient coefficient)
cubicAuditScaleClosedForm coefficient = solve (coefficient ∷ [])

absorptionGapIdentity :
  ∀ coefficient →
  absorptionGap coefficient
  ≡ 6 * SR.square (scaleForCoefficient coefficient)
absorptionGapIdentity coefficient = solve (coefficient ∷ [])

onePositive : 0ℚ < 1ℚ
onePositive = ℚₚ.positive⁻¹ 1ℚ

scaleForNonnegativeCoefficientPositive :
  ∀ coefficient →
  0ℚ ≤ coefficient →
  0ℚ < scaleForCoefficient coefficient
scaleForNonnegativeCoefficientPositive coefficient coefficientNonnegative =
  let
    shifted : 0ℚ + 0ℚ < coefficient + 1ℚ
    shifted = ℚₚ.+-mono-≤-< coefficientNonnegative onePositive
  in
  subst
    (λ lower → lower < scaleForCoefficient coefficient)
    (ℚₚ.+-identityˡ 0ℚ)
    shifted

sixPositive : 0ℚ < 6
sixPositive = ℚₚ.positive⁻¹ 6

absorptionGapPositive :
  ∀ coefficient →
  0ℚ ≤ coefficient →
  0ℚ < absorptionGap coefficient
absorptionGapPositive coefficient coefficientNonnegative =
  let
    scale = scaleForCoefficient coefficient
    scalePositive =
      scaleForNonnegativeCoefficientPositive
        coefficient coefficientNonnegative

    instance
      scalePositiveInstance = positive scalePositive
      scaleSquaredPositiveInstance = ℚₚ.pos*pos⇒pos scale scale
      sixPositiveInstance = positive sixPositive
      gapModelPositiveInstance =
        ℚₚ.pos*pos⇒pos 6 (SR.square scale)

    modelPositive : 0ℚ < 6 * SR.square scale
    modelPositive = ℚₚ.positive⁻¹ (6 * SR.square scale)
  in
  subst
    (λ value → 0ℚ < value)
    (sym (absorptionGapIdentity coefficient))
    modelPositive

coefficientTimesQuadraticPlusGapEqualsCubic :
  ∀ coefficient →
  coefficient * quadraticAtAuditScale coefficient
    + absorptionGap coefficient
  ≡ cubicAtAuditScale coefficient
coefficientTimesQuadraticPlusGapEqualsCubic coefficient =
  solve (coefficient ∷ [])

cubicExceedsEveryNonnegativeQuadraticCoefficient :
  ∀ coefficient →
  0ℚ ≤ coefficient →
  coefficient * quadraticAtAuditScale coefficient
  < cubicAtAuditScale coefficient
cubicExceedsEveryNonnegativeQuadraticCoefficient
  coefficient coefficientNonnegative =
  let
    weightedQuadratic =
      coefficient * quadraticAtAuditScale coefficient
    gap = absorptionGap coefficient

    withGap : weightedQuadratic + 0ℚ < weightedQuadratic + gap
    withGap =
      ℚₚ.+-monoʳ-< weightedQuadratic
        (absorptionGapPositive coefficient coefficientNonnegative)

    normalizedLeft : weightedQuadratic < weightedQuadratic + gap
    normalizedLeft =
      subst
        (λ left → left < weightedQuadratic + gap)
        (ℚₚ.+-identityʳ weightedQuadratic)
        withGap
  in
  subst
    (λ right → weightedQuadratic < right)
    (coefficientTimesQuadraticPlusGapEqualsCubic coefficient)
    normalizedLeft

record SpectralAbsorptionAuditConclusion : Set where
  constructor spectralAbsorptionAuditConclusion
  field
    quadraticMagnitudeDeterminesCubicOrientation : Set
    universalScaleFreeCubicByQuadraticCoefficientExists : Set
    quadraticProjectionFailureWitnessed :
      quadraticMagnitudeDeterminesCubicOrientation → Set
    scalingFailureWitnessed :
      universalScaleFreeCubicByQuadraticCoefficientExists → Set

canonicalSpectralAbsorptionAuditConclusion :
  SpectralAbsorptionAuditConclusion
canonicalSpectralAbsorptionAuditConclusion =
  spectralAbsorptionAuditConclusion
    ⊥
    ⊥
    (λ impossible → ⊥)
    (λ impossible → ⊥)
  where
  open import Data.Empty using (⊥)
