module DASHI.Foundations.SpectralCountingComplexity where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)

------------------------------------------------------------------------
-- Weyl-law-facing spectral accounting.
--
-- This generic package separates discrete/cuspidal mass, continuous/scattering
-- mass, the principal geometric Weyl term, and the remainder.  It does not
-- promote an automorphic Weyl theorem until a concrete spectral authority
-- supplies the decomposition and asymptotic estimate.

record SpectralScalar : Set₁ where
  field
    Scalar : Set
    zero one : Scalar
    add mul : Scalar → Scalar → Scalar
    log : Scalar → Scalar
    LessEqual : Scalar → Scalar → Set

open SpectralScalar public

record SpectralCountingPackage
  (Scale : Set)
  (S : SpectralScalar) : Set₁ where
  field
    cutoff : Scale

    discreteCount : Scale → Nat
    discreteMass : Scale → Scalar S
    continuousMass : Scale → Scalar S
    residualMass : Scale → Scalar S
    totalSpectralMass : Scale → Scalar S
    principalWeylTerm : Scale → Scalar S

    countingDecomposition :
      ∀ Λ →
      totalSpectralMass Λ
      ≡ add S
          (discreteMass Λ)
          (add S (continuousMass Λ) (residualMass Λ))

    principalPlusRemainder :
      ∀ Λ →
      totalSpectralMass Λ
      ≡ add S (principalWeylTerm Λ) (residualMass Λ)

open SpectralCountingPackage public

record WeylAsymptoticControl
  {Scale : Set}
  {S : SpectralScalar}
  (P : SpectralCountingPackage Scale S) : Set₁ where
  field
    remainderBound : Scale → Scalar S
    absoluteRemainder : Scale → Scalar S

    remainderControlled :
      ∀ Λ →
      LessEqual S (absoluteRemainder Λ) (remainderBound Λ)

    asymptoticRegime : Scale → Set

open WeylAsymptoticControl public

record SpectralMDLComplexityBudget
  {Scale : Set}
  {S : SpectralScalar}
  (P : SpectralCountingPackage Scale S) : Set₁ where
  field
    countAsScalar : Nat → Scalar S
    descriptionComplexity : Scale → Scalar S
    geometryCorrection : Scale → Scalar S

    complexityFromSpectralCardinality :
      ∀ Λ →
      descriptionComplexity Λ
      ≡ add S
          (log S (countAsScalar (discreteCount P Λ)))
          (geometryCorrection Λ)

open SpectralMDLComplexityBudget public

------------------------------------------------------------------------
-- Noncompact automorphic boundary: cusp forms and continuous spectrum must not
-- be silently conflated.

data SpectralRegime : Set where
  compactRegime : SpectralRegime
  finiteVolumeNoncompactRegime : SpectralRegime

record AutomorphicWeylBoundary : Set₁ where
  field
    regime : SpectralRegime
    cuspFormsSeparated : Bool
    continuousSpectrumSeparated : Bool
    scatteringContributionTracked : Bool
    fullAutomorphicWeylLawPromoted : Bool

    cuspFormsSeparatedIsTrue : cuspFormsSeparated ≡ true
    continuousSpectrumSeparatedIsTrue :
      continuousSpectrumSeparated ≡ true
    scatteringContributionTrackedIsTrue :
      scatteringContributionTracked ≡ true

open AutomorphicWeylBoundary public

candidateAutomorphicWeylBoundary : AutomorphicWeylBoundary
candidateAutomorphicWeylBoundary =
  record
    { regime = finiteVolumeNoncompactRegime
    ; cuspFormsSeparated = true
    ; continuousSpectrumSeparated = true
    ; scatteringContributionTracked = true
    ; fullAutomorphicWeylLawPromoted = false
    ; cuspFormsSeparatedIsTrue = refl
    ; continuousSpectrumSeparatedIsTrue = refl
    ; scatteringContributionTrackedIsTrue = refl
    }
