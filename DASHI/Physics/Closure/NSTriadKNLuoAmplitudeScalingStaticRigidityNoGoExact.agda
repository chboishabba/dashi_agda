module DASHI.Physics.Closure.NSTriadKNLuoAmplitudeScalingStaticRigidityNoGoExact where

------------------------------------------------------------------------
-- PRIMARY AUDIT TARGET
--
-- Ryusho Nemoto,
-- "Global Regularity of the Three-Dimensional Navier-Stokes Equations via
-- a Coupled Energy and Stability Framework".
-- PhilArchive record: NEMGRO. DOI: none located.
-- Status: manuscript/preprint and audit target only.
--
-- DASHI CONTRIBUTION
--
-- A positive-strain response is cubic under amplitude scaling, whereas
-- Laplacian dissipation is quadratic.  Using the explicit positive core from
-- NSTriadKNLuoCompactSupportPositiveStrainCoreExact, normalize the base core
-- response to the checked value 8 and let d >= 0 denote its finite Laplacian
-- energy.  For every proposed coefficient C >= 0 choose
--
--   r = C d + 1.
--
-- Then the exact gap is
--
--   8 r^3 - C r^2 d = r^2 (7 C d + 8) > 0.
--
-- Hence no universal scale-free coefficient can bound the cubic response by
-- the quadratic dissipation on every amplitude rescaling.  This is the
-- homogeneous obstruction behind the full physical counterexample.
------------------------------------------------------------------------

open import Agda.Builtin.List using ([]; _∷_)
open import Data.Rational.Base using
  (ℚ; 0ℚ; 1ℚ; _+_; _*_; _-_; _≤_; _<_; positive; nonNegative)
import Data.Rational.Properties as ℚₚ
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (_≡_; subst; sym)

import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as L2
import DASHI.Physics.Closure.NSTriadKNLuoCompactSupportPositiveStrainCoreExact as Core

square : ℚ → ℚ
square = L2.square

cube : ℚ → ℚ
cube value = value * value * value

record StaticRigidityCandidate : Set where
  constructor staticRigidityCandidate
  field
    coefficient baseDissipation : ℚ
    coefficientNonnegative : 0ℚ ≤ coefficient
    baseDissipationNonnegative : 0ℚ ≤ baseDissipation

open StaticRigidityCandidate public

amplitudeScale : StaticRigidityCandidate → ℚ
amplitudeScale candidate =
  coefficient candidate * baseDissipation candidate + 1ℚ

scaledPositiveResponse : StaticRigidityCandidate → ℚ
scaledPositiveResponse candidate =
  8 * cube (amplitudeScale candidate)

scaledRigidityRightHandSide : StaticRigidityCandidate → ℚ
scaledRigidityRightHandSide candidate =
  coefficient candidate
  * square (amplitudeScale candidate)
  * baseDissipation candidate

scalingGap : StaticRigidityCandidate → ℚ
scalingGap candidate =
  scaledPositiveResponse candidate
  - scaledRigidityRightHandSide candidate

scalingGapIdentity :
  ∀ candidate →
  scalingGap candidate
  ≡
  square (amplitudeScale candidate)
  * ( 7 * coefficient candidate * baseDissipation candidate + 8 )
scalingGapIdentity candidate =
  solve
    ( coefficient candidate
    ∷ baseDissipation candidate
    ∷ [])

coefficientTimesDissipationNonnegative :
  ∀ candidate →
  0ℚ ≤ coefficient candidate * baseDissipation candidate
coefficientTimesDissipationNonnegative candidate =
  let
    instance
      coefficientNN = nonNegative (coefficientNonnegative candidate)
      dissipationNN =
        nonNegative (baseDissipationNonnegative candidate)
      productNN =
        ℚₚ.nonNeg*nonNeg⇒nonNeg
          (coefficient candidate)
          (baseDissipation candidate)
  in
  ℚₚ.nonNegative⁻¹
    (coefficient candidate * baseDissipation candidate)

amplitudeScalePositive :
  ∀ candidate → 0ℚ < amplitudeScale candidate
amplitudeScalePositive candidate =
  let
    onePositive : 0ℚ < 1ℚ
    onePositive = ℚₚ.positive⁻¹ 1ℚ

    shifted :
      0ℚ + 0ℚ
      < coefficient candidate * baseDissipation candidate + 1ℚ
    shifted =
      ℚₚ.+-mono-≤-<
        (coefficientTimesDissipationNonnegative candidate)
        onePositive
  in
  subst
    (λ left → left < amplitudeScale candidate)
    (ℚₚ.+-identityˡ 0ℚ)
    shifted

sevenNonnegative : 0ℚ ≤ 7
sevenNonnegative =
  let
    sevenPositive : 0ℚ < 7
    sevenPositive = ℚₚ.positive⁻¹ 7

    instance
      sevenPositiveInstance = positive sevenPositive
      sevenNonnegativeInstance = ℚₚ.pos⇒nonNeg 7
  in
  ℚₚ.nonNegative⁻¹ 7

sevenProductNonnegative :
  ∀ candidate →
  0ℚ ≤ 7 * coefficient candidate * baseDissipation candidate
sevenProductNonnegative candidate =
  let
    instance
      sevenNN = nonNegative sevenNonnegative
      coefficientNN = nonNegative (coefficientNonnegative candidate)
      firstProductNN =
        ℚₚ.nonNeg*nonNeg⇒nonNeg 7 (coefficient candidate)
      dissipationNN =
        nonNegative (baseDissipationNonnegative candidate)
      secondProductNN =
        ℚₚ.nonNeg*nonNeg⇒nonNeg
          (7 * coefficient candidate)
          (baseDissipation candidate)
  in
  ℚₚ.nonNegative⁻¹
    (7 * coefficient candidate * baseDissipation candidate)

scalingBracketPositive :
  ∀ candidate →
  0ℚ < 7 * coefficient candidate * baseDissipation candidate + 8
scalingBracketPositive candidate =
  let
    eightPositive : 0ℚ < 8
    eightPositive = ℚₚ.positive⁻¹ 8

    shifted :
      0ℚ + 0ℚ
      < 7 * coefficient candidate * baseDissipation candidate + 8
    shifted =
      ℚₚ.+-mono-≤-<
        (sevenProductNonnegative candidate)
        eightPositive
  in
  subst
    (λ left →
      left
      < 7 * coefficient candidate * baseDissipation candidate + 8)
    (ℚₚ.+-identityˡ 0ℚ)
    shifted

scalingGapPositive :
  ∀ candidate → 0ℚ < scalingGap candidate
scalingGapPositive candidate =
  let
    scale = amplitudeScale candidate
    scalePositive = amplitudeScalePositive candidate
    bracket =
      7 * coefficient candidate * baseDissipation candidate + 8
    bracketPositive = scalingBracketPositive candidate

    instance
      scalePositiveInstance = positive scalePositive
      scaleSquaredPositiveInstance = ℚₚ.pos*pos⇒pos scale scale
      bracketPositiveInstance = positive bracketPositive
      gapModelPositiveInstance =
        ℚₚ.pos*pos⇒pos (square scale) bracket

    modelPositive : 0ℚ < square scale * bracket
    modelPositive = ℚₚ.positive⁻¹ (square scale * bracket)
  in
  subst
    (λ value → 0ℚ < value)
    (sym (scalingGapIdentity candidate))
    modelPositive

rightPlusGapEqualsResponse :
  ∀ candidate →
  scaledRigidityRightHandSide candidate + scalingGap candidate
  ≡ scaledPositiveResponse candidate
rightPlusGapEqualsResponse candidate =
  solve
    ( coefficient candidate
    ∷ baseDissipation candidate
    ∷ [])

staticRigidityFailsAtExplicitAmplitude :
  ∀ candidate →
  scaledRigidityRightHandSide candidate
  < scaledPositiveResponse candidate
staticRigidityFailsAtExplicitAmplitude candidate =
  let
    right = scaledRigidityRightHandSide candidate
    gap = scalingGap candidate

    withGap : right + 0ℚ < right + gap
    withGap =
      ℚₚ.+-monoʳ-< right (scalingGapPositive candidate)

    leftClosed : right + 0ℚ ≡ right
    leftClosed = solve (right ∷ [])

    normalized : right < right + gap
    normalized =
      subst
        (λ left → left < right + gap)
        leftClosed
        withGap
  in
  subst
    (λ upper → right < upper)
    (rightPlusGapEqualsResponse candidate)
    normalized

checkedCoreResponse :
  Core.totalPositiveStrainResponse Core.unitCoreLedger ≡ 8
checkedCoreResponse = Core.unitCoreResponseIsEight

record AmplitudeScalingAuditConclusion : Set where
  constructor amplitudeScalingAuditConclusion
  field
    cubicResponseScalingProved : Set
    quadraticDissipationScalingProved : Set
    universalStaticCoefficientSurvivesScaling : Set

canonicalAmplitudeScalingAuditConclusion :
  AmplitudeScalingAuditConclusion
canonicalAmplitudeScalingAuditConclusion =
  amplitudeScalingAuditConclusion ⊤ ⊤ ⊥
  where
  open import Data.Unit using (⊤)
  open import Data.Empty using (⊥)
