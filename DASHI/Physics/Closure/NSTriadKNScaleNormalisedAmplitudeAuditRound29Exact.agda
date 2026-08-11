module DASHI.Physics.Closure.NSTriadKNScaleNormalisedAmplitudeAuditRound29Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Authors: Hajer Bahouri; Jean-Yves Chemin; Raphael Danchin.
-- Title: "Fourier Analysis and Nonlinear Partial Differential Equations".
-- DOI: 10.1007/978-3-642-16830-7.
--
-- DASHI CONTRIBUTION
--
-- Raw three-dimensional Bernstein amplitude has one scale power more than the
-- quadratic viscous quantity. This file proves exactly that multiplying by one
-- inverse shell scale removes that homogeneity gap. It does not manufacture a
-- small coefficient or a physical bad-set estimate.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using ([]; _∷_)
open import Data.Rational.Base using (ℚ; 1ℚ; _*_)
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (cong; trans)

record InverseShellScale : Set where
  constructor inverse-shell-scale
  field
    shellScale inverseScale : ℚ
    inverseLaw : inverseScale * shellScale ≡ 1ℚ

open InverseShellScale public

rawCubicAmplitude : InverseShellScale → ℚ → ℚ
rawCubicAmplitude scale energy =
  shellScale scale * shellScale scale * shellScale scale * energy

scaleNormalisedAmplitude : InverseShellScale → ℚ → ℚ
scaleNormalisedAmplitude scale energy =
  inverseScale scale * rawCubicAmplitude scale energy

quadraticDiffusionScale : InverseShellScale → ℚ → ℚ
quadraticDiffusionScale scale energy =
  shellScale scale * shellScale scale * energy

oneInverseScaleRepairsHomogeneity :
  (scale : InverseShellScale) →
  (energy : ℚ) →
  scaleNormalisedAmplitude scale energy
  ≡ quadraticDiffusionScale scale energy
oneInverseScaleRepairsHomogeneity scale energy =
  trans
    (solve
      ( inverseScale scale
      ∷ shellScale scale
      ∷ energy
      ∷ []))
    (trans
      (cong
        (λ product →
          product *
          (shellScale scale * shellScale scale * energy))
        (inverseLaw scale))
      (solve (shellScale scale ∷ energy ∷ [])))

record ParameterisedBadAmplitudeCandidate : Set where
  constructor parameterised-bad-amplitude-candidate
  field
    scale : InverseShellScale
    shellEnergy : ℚ
    candidateAmplitude : ℚ
    candidateMeaning :
      candidateAmplitude
      ≡ scaleNormalisedAmplitude scale shellEnergy

open ParameterisedBadAmplitudeCandidate public

candidateHasCriticalHomogeneity :
  (candidate : ParameterisedBadAmplitudeCandidate) →
  candidateAmplitude candidate
  ≡ quadraticDiffusionScale (scale candidate) (shellEnergy candidate)
candidateHasCriticalHomogeneity candidate =
  trans
    (candidateMeaning candidate)
    (oneInverseScaleRepairsHomogeneity
      (scale candidate) (shellEnergy candidate))

scaleNormalisedAmplitudeHomogeneityClosed : Bool
scaleNormalisedAmplitudeHomogeneityClosed = true

physicalBadAmplitudeSquareBudgetClosed : Bool
physicalBadAmplitudeSquareBudgetClosed = false

scaleNormalisedAmplitudeHomogeneityClosedIsTrue :
  scaleNormalisedAmplitudeHomogeneityClosed ≡ true
scaleNormalisedAmplitudeHomogeneityClosedIsTrue = refl

physicalBadAmplitudeSquareBudgetClosedIsFalse :
  physicalBadAmplitudeSquareBudgetClosed ≡ false
physicalBadAmplitudeSquareBudgetClosedIsFalse = refl
