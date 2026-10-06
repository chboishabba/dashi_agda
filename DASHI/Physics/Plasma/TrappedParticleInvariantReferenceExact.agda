module DASHI.Physics.Plasma.TrappedParticleInvariantReferenceExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- TRAPPED-PARTICLE INVARIANT REFERENCE
--
-- The primary comparison object is not an architecture label.  It is a
-- source-/artifact-backed trapped-particle invariant profile.  Omnigenity is
-- represented through second-adiabatic-invariant / bounce-radial-drift defect;
-- maximum-J quality is an additional coordinate, not silently identified with
-- omnigenity.
------------------------------------------------------------------------

record TrappedParticleInvariantProfile : Set₁ where
  constructor trapped-particle-invariant-profile
  field
    secondAdiabaticInvariantReceipt : Set
    bounceAveragedRadialDriftReceipt : Set
    maximumJReceipt : Set
    pitchAndFieldLineCoverageReceipt : Set
    finiteOrbitWidthReceipt : Set
    energeticParticleReceipt : Set

    -- Lower Nat means lower declared defect/burden on the same comparison chart.
    bounceActionFieldLineDefectCost : Nat
    bounceAveragedRadialDriftDefectCost : Nat
    maximumJViolationCost : Nat
    effectiveRippleOrNeoclassicalDefectCost : Nat
    energeticParticleLossDefectCost : Nat

    metricNormalizationReference : String
    equilibriumReference : String
    invariantReference : String

open TrappedParticleInvariantProfile public

record SameOrBetterTrappedParticleInvariant
    (candidate reference : TrappedParticleInvariantProfile) : Set₁ where
  constructor same-or-better-trapped-particle-invariant
  field
    noWorseBounceActionFieldLineDefect :
      bounceActionFieldLineDefectCost candidate ≤
      bounceActionFieldLineDefectCost reference
    noWorseBounceAveragedRadialDriftDefect :
      bounceAveragedRadialDriftDefectCost candidate ≤
      bounceAveragedRadialDriftDefectCost reference
    noWorseMaximumJViolation :
      maximumJViolationCost candidate ≤ maximumJViolationCost reference
    noWorseEffectiveRippleOrNeoclassicalDefect :
      effectiveRippleOrNeoclassicalDefectCost candidate ≤
      effectiveRippleOrNeoclassicalDefectCost reference
    noWorseEnergeticParticleLoss :
      energeticParticleLossDefectCost candidate ≤
      energeticParticleLossDefectCost reference

    samePitchClassCoverageReceipt : Set
    sameRadialDomainReceipt : Set
    sameEquilibriumRegimeReceipt : Set
    sameMetricNormalizationReceipt : Set
    sameEvidenceStandardReceipt : Set
    atLeastOneStrictImprovementReceipt : Set
    comparisonReference : String

open SameOrBetterTrappedParticleInvariant public

record TrappedParticleInvariantBoundary : Set where
  constructor trapped-particle-invariant-boundary
  field
    omnigenityAloneImpliesMaximumJ : Bool
    omnigenityAloneImpliesMaximumJIsFalse :
      omnigenityAloneImpliesMaximumJ ≡ false

    maximumJAloneImpliesCommercialPlant : Bool
    maximumJAloneImpliesCommercialPlantIsFalse :
      maximumJAloneImpliesCommercialPlant ≡ false

    architectureLabelAloneOrdersTrappedParticleQuality : Bool
    architectureLabelAloneOrdersTrappedParticleQualityIsFalse :
      architectureLabelAloneOrdersTrappedParticleQuality ≡ false

    sameOrBetterRequiresSameComparisonChart : Bool
    sameOrBetterRequiresSameComparisonChartIsTrue :
      sameOrBetterRequiresSameComparisonChart ≡ true

canonicalTrappedParticleInvariantBoundary : TrappedParticleInvariantBoundary
canonicalTrappedParticleInvariantBoundary =
  trapped-particle-invariant-boundary
    false refl
    false refl
    false refl
    true refl
