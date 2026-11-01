module DASHI.Physics.Closure.NSTriadKNLuoHighFrequencyApproximationUniformGradientNoGoExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / AUDIT CONTEXT
--
-- Ryusho Nemoto,
-- "Global Regularity of the Three-Dimensional Navier-Stokes Equations via
-- a Coupled Energy and Stability Framework".
-- PhilArchive record: NEMGRO. DOI: none located.
-- Status: manuscript/preprint and audit target only.
--
-- Roger Temam,
-- "Navier-Stokes Equations: Theory and Numerical Analysis".
-- DOI: 10.1090/chel/343.
--
-- DASHI CONTRIBUTION
--
-- Convergence of smooth initial data in L2 does not supply a uniform H1
-- bound.  The exact high-frequency model chooses, for any threshold M >= 0,
--
--   q = M + 1,
--   amplitude = 1/q,
--   frequency = q^2.
--
-- The L2 perturbation amplitude is reciprocal in q, while its gradient
-- amplitude is
--
--   q^2 * (1/q) = q = M+1 > M.
--
-- Thus arbitrarily accurate high-frequency perturbations can carry gradient
-- data above any prescribed threshold.  The manuscript's smooth-approximation
-- passage cannot obtain a uniform initial coupled-functional bound from L2
-- convergence alone.
------------------------------------------------------------------------

open import Agda.Builtin.List using ([]; _∷_)
open import Data.Rational.Base as ℚ using
  (ℚ; 0ℚ; 1ℚ; _+_; _*_; _≤_; _<_; 1/_; positive)
import Data.Rational.Properties as ℚₚ
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (_≡_; cong; subst; sym; trans)

record GradientThreshold : Set where
  constructor gradientThreshold
  field
    threshold : ℚ
    thresholdNonnegative : 0ℚ ≤ threshold

open GradientThreshold public

frequencyScale : GradientThreshold → ℚ
frequencyScale candidate = threshold candidate + 1ℚ

frequencyScalePositive :
  ∀ candidate → 0ℚ < frequencyScale candidate
frequencyScalePositive candidate =
  let
    onePositive : 0ℚ < 1ℚ
    onePositive = ℚₚ.positive⁻¹ 1ℚ

    shifted : 0ℚ + 0ℚ < threshold candidate + 1ℚ
    shifted =
      ℚₚ.+-mono-≤-<
        (thresholdNonnegative candidate)
        onePositive
  in
  subst
    (λ left → left < frequencyScale candidate)
    (ℚₚ.+-identityˡ 0ℚ)
    shifted

perturbationAmplitude : GradientThreshold → ℚ
perturbationAmplitude candidate =
  let
    scale = frequencyScale candidate
    scalePositive = frequencyScalePositive candidate
    instance
      scaleNonzero = ℚ.>-nonZero scalePositive
  in
  ℚ.1/_ scale

perturbationFrequency : GradientThreshold → ℚ
perturbationFrequency candidate =
  frequencyScale candidate * frequencyScale candidate

perturbationGradientAmplitude : GradientThreshold → ℚ
perturbationGradientAmplitude candidate =
  perturbationFrequency candidate * perturbationAmplitude candidate

scaleTimesAmplitudeIsOne :
  ∀ candidate →
  frequencyScale candidate * perturbationAmplitude candidate ≡ 1ℚ
scaleTimesAmplitudeIsOne candidate =
  let
    scale = frequencyScale candidate
    scalePositive = frequencyScalePositive candidate
    instance
      scaleNonzero = ℚ.>-nonZero scalePositive
  in
  ℚₚ.*-inverseʳ scale

highFrequencyGradientClosedForm :
  ∀ candidate →
  perturbationGradientAmplitude candidate ≡ frequencyScale candidate
highFrequencyGradientClosedForm candidate =
  let
    scale = frequencyScale candidate
    amplitude = perturbationAmplitude candidate

    reassociated :
      (scale * scale) * amplitude
      ≡ scale * (scale * amplitude)
    reassociated = solve (scale ∷ amplitude ∷ [])

    normalized :
      scale * (scale * amplitude)
      ≡ scale * 1ℚ
    normalized =
      cong (λ factor → scale * factor)
        (scaleTimesAmplitudeIsOne candidate)

    unitClosed : scale * 1ℚ ≡ scale
    unitClosed = solve (scale ∷ [])
  in
  trans reassociated (trans normalized unitClosed)

frequencyScaleExceedsThreshold :
  ∀ candidate → threshold candidate < frequencyScale candidate
frequencyScaleExceedsThreshold candidate =
  let
    onePositive : 0ℚ < 1ℚ
    onePositive = ℚₚ.positive⁻¹ 1ℚ

    shifted :
      threshold candidate + 0ℚ
      < threshold candidate + 1ℚ
    shifted = ℚₚ.+-monoʳ-< (threshold candidate) onePositive

    leftClosed : threshold candidate + 0ℚ ≡ threshold candidate
    leftClosed = solve (threshold candidate ∷ [])
  in
  subst
    (λ left → left < frequencyScale candidate)
    leftClosed
    shifted

highFrequencyGradientExceedsEveryThreshold :
  ∀ candidate →
  threshold candidate < perturbationGradientAmplitude candidate
highFrequencyGradientExceedsEveryThreshold candidate =
  subst
    (λ right → threshold candidate < right)
    (sym (highFrequencyGradientClosedForm candidate))
    (frequencyScaleExceedsThreshold candidate)

perturbationAmplitudePositive :
  ∀ candidate → 0ℚ < perturbationAmplitude candidate
perturbationAmplitudePositive candidate =
  let
    scale = frequencyScale candidate
    scalePositive = frequencyScalePositive candidate
    instance
      scalePositiveInstance = positive scalePositive
      scaleNonzero = ℚₚ.pos⇒nonZero scale
      inversePositive = ℚₚ.1/pos⇒pos scale
  in
  ℚₚ.positive⁻¹ (perturbationAmplitude candidate)

record ApproximationAuditConclusion : Set where
  constructor approximationAuditConclusion
  field
    reciprocalL2PerturbationConstructed : Set
    gradientAboveArbitraryThresholdConstructed : Set
    L2ConvergenceSuppliesUniformInitialH1 : Set
    weakLowerSemicontinuityOfCubicSpectralFunctionalEstablished : Set

canonicalApproximationAuditConclusion : ApproximationAuditConclusion
canonicalApproximationAuditConclusion =
  approximationAuditConclusion ⊤ ⊤ ⊥ ⊥
  where
  open import Data.Unit using (⊤)
  open import Data.Empty using (⊥)
