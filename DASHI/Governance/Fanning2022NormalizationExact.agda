module DASHI.Governance.Fanning2022NormalizationExact where

open import DASHI.Core.Prelude
import DASHI.Governance.Fanning2022TemporalIndicatorExact as Fanning
import DASHI.Governance.SafeJustSourceRegistryExact as Sources

------------------------------------------------------------------------
-- FANNING ET AL. 2022: NORMALIZATION / SHORTFALL / OVERSHOOT AUTHORITY
--
-- Source formulas:
--
--   biophysical:  x'_t = x_t / x*_t
--
--     x*_t is the per-capita biophysical boundary in year t.  The absolute
--     per-capita boundary therefore changes with population.
--
--   social:       y'_t = (y_t - y_min) / (y* - y_min)
--
--     y* is the fixed social threshold and y_min is the lowest observed value
--     for that social indicator over the 1992--2015 analysis period.
--
-- Both normalizations put the relevant threshold/boundary at 1, but they do
-- not have the same denominator authority.  The exact source formulas are
-- recorded structurally below.  The Nat arithmetic later in this module is a
-- finite fixed-point shadow with 100 = normalized 1; it is NOT a numerical
-- reconstruction of the empirical dataset.
--
-- Shortfall / overshoot components:
--
--   social:       s_i = max(0, 1 - y'_i)
--   ecological:   e_j = max(0, x'_j - 1)
--
-- Each domain index is the unweighted average of its transformed components.
-- This averaging permits compensation WITHIN a domain.  The paper nevertheless
-- keeps social shortfall and ecological overshoot as two separate indices,
-- rather than allowing cross-domain compensation through one scalar.
------------------------------------------------------------------------

data NormalizationAuthority : Set where
  timeIndexedBiophysicalBoundary observedPeriodSocialMinimum : NormalizationAuthority

record BiophysicalNormalizationSpec : Set where
  constructor biophysicalNormalizationSpec
  field
    rawValueRole : Nat
    timeIndexedBoundaryRole : Nat

record SocialNormalizationSpec : Set where
  constructor socialNormalizationSpec
  field
    rawValueRole : Nat
    fixedThresholdRole : Nat
    observedPeriodMinimumRole : Nat

biophysicalNormalizationAuthority : NormalizationAuthority
biophysicalNormalizationAuthority = timeIndexedBiophysicalBoundary

socialNormalizationAuthority : NormalizationAuthority
socialNormalizationAuthority = observedPeriodSocialMinimum

normalizationAuthoritiesDiffer :
  biophysicalNormalizationAuthority ≡ socialNormalizationAuthority → ⊥
normalizationAuthoritiesDiffer ()

------------------------------------------------------------------------
-- Fixed-point finite shadow: 100 represents normalized threshold/boundary 1.
------------------------------------------------------------------------

normalizedOne : Nat
normalizedOne = 100

socialShortfallComponent : Nat → Nat
socialShortfallComponent normalized = normalizedOne ∸ normalized

ecologicalOvershootComponent : Nat → Nat
ecologicalOvershootComponent normalized = normalized ∸ normalizedOne

socialBelow socialAt socialAbove : Nat
socialBelow = 70
socialAt = 100
socialAbove = 130

ecoBelow ecoAt ecoAbove : Nat
ecoBelow = 70
ecoAt = 100
ecoAbove = 130

socialBelowShortfall : socialShortfallComponent socialBelow ≡ 30
socialBelowShortfall = refl

socialAtHasNoShortfall : socialShortfallComponent socialAt ≡ 0
socialAtHasNoShortfall = refl

socialAboveHasNoShortfall : socialShortfallComponent socialAbove ≡ 0
socialAboveHasNoShortfall = refl

ecoBelowHasNoOvershoot : ecologicalOvershootComponent ecoBelow ≡ 0
ecoBelowHasNoOvershoot = refl

ecoAtHasNoOvershoot : ecologicalOvershootComponent ecoAt ≡ 0
ecoAtHasNoOvershoot = refl

ecoAboveOvershoot : ecologicalOvershootComponent ecoAbove ≡ 30
ecoAboveOvershoot = refl

------------------------------------------------------------------------
-- Unweighted-average authority without silently importing Nat division.
-- `sumCode / countCode` is the intended mathematical average; this exact core
-- retains numerator and denominator separately.
------------------------------------------------------------------------

record AverageCode : Set where
  constructor averageCode
  field
    sumCode : Nat
    countCode : Nat

open AverageCode public

pairAverageCode : Nat → Nat → AverageCode
pairAverageCode left right = averageCode (left + right) 2

-- Two different coordinate allocations have the same average code.
withinDomainA withinDomainB : AverageCode
withinDomainA = pairAverageCode 30 0
withinDomainB = pairAverageCode 0 30

sameWithinDomainAverageCode : withinDomainA ≡ withinDomainB
sameWithinDomainAverageCode = refl

-- But the first coordinate is different; equality of the average does not
-- reconstruct the residual vector.
firstA firstB : Nat
firstA = 30
firstB = 0

sameAverageDoesNotRecoverFirstCoordinate : firstA ≡ firstB → ⊥
sameAverageDoesNotRecoverFirstCoordinate ()

------------------------------------------------------------------------
-- Cross-domain non-compensation: retain two indices as a product state.
------------------------------------------------------------------------

record SafeJustExtent : Set where
  constructor safeJustExtent
  field
    socialShortfall : AverageCode
    ecologicalOvershoot : AverageCode

open SafeJustExtent public

socialHeavy ecoHeavy : SafeJustExtent
socialHeavy = safeJustExtent (averageCode 60 2) (averageCode 20 2)
ecoHeavy = safeJustExtent (averageCode 20 2) (averageCode 60 2)

-- Their combined numerators coincide, but the safe-and-just extent states do
-- not.  This is the finite analogue of why cross-domain compensation is not an
-- admissible replacement for the two-index view.
combinedNumerator : SafeJustExtent → Nat
combinedNumerator e = sumCode (socialShortfall e) + sumCode (ecologicalOvershoot e)

sameCombinedNumerator : combinedNumerator socialHeavy ≡ combinedNumerator ecoHeavy
sameCombinedNumerator = refl

combinedScalarDoesNotRecoverSocialExtent :
  sumCode (socialShortfall socialHeavy) ≡ sumCode (socialShortfall ecoHeavy) → ⊥
combinedScalarDoesNotRecoverSocialExtent ()

source : Sources.SourceReference
source = Sources.fanning2022

record FanningNormalizationBoundary : Set where
  constructor fanningNormalizationBoundary
  field
    biophysicalDenominatorIsTimeIndexedBoundary : Bool
    biophysicalDenominatorIsTimeIndexedBoundaryIsTrue :
      biophysicalDenominatorIsTimeIndexedBoundary ≡ true
    socialDenominatorUsesObservedPeriodMinimum : Bool
    socialDenominatorUsesObservedPeriodMinimumIsTrue :
      socialDenominatorUsesObservedPeriodMinimum ≡ true
    sameNormalizedThresholdImpliesSameNormalizationAuthority : Bool
    sameNormalizedThresholdImpliesSameNormalizationAuthorityIsFalse :
      sameNormalizedThresholdImpliesSameNormalizationAuthority ≡ false
    withinDomainAveragePermitsCompensation : Bool
    withinDomainAveragePermitsCompensationIsTrue :
      withinDomainAveragePermitsCompensation ≡ true
    withinDomainAverageRecoversResidualVector : Bool
    withinDomainAverageRecoversResidualVectorIsFalse :
      withinDomainAverageRecoversResidualVector ≡ false
    socialAndEcologicalIndicesAreCollapsedIntoOneCompensatoryScalar : Bool
    socialAndEcologicalIndicesAreCollapsedIntoOneCompensatoryScalarIsFalse :
      socialAndEcologicalIndicesAreCollapsedIntoOneCompensatoryScalar ≡ false
    finiteHundredScaleIsEmpiricalDatasetReconstruction : Bool
    finiteHundredScaleIsEmpiricalDatasetReconstructionIsFalse :
      finiteHundredScaleIsEmpiricalDatasetReconstruction ≡ false

canonicalFanningNormalizationBoundary : FanningNormalizationBoundary
canonicalFanningNormalizationBoundary =
  fanningNormalizationBoundary
    true refl
    true refl
    false refl
    true refl
    false refl
    false refl
    false refl
