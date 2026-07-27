module DASHI.Physics.YangMills.BalabanClayT2ClusterCriterionComparisonExact where

open import Data.Rational using (ℚ; 0ℚ; _*_; _≤_)

open import DASHI.Physics.YangMills.CompactLieProofLevel

------------------------------------------------------------------------
-- Literature normalization.
--
-- R. Kotecký and D. Preiss,
-- "Cluster expansion for abstract polymer models",
-- Communications in Mathematical Physics 103 (1986), 491--498.
-- DOI: 10.1007/BF01211762
--
-- R. Fernández and A. Procacci,
-- "Cluster expansion for abstract polymer models. New bounds from an old
-- approach",
-- Communications in Mathematical Physics 274 (2007), 123--140.
-- DOI: 10.1007/s00220-007-0279-2
--
-- R. Bissacot, R. Fernández and A. Procacci,
-- "On the convergence of cluster expansions for polymer gases",
-- Journal of Statistical Physics 139 (2010), 598--617.
-- DOI: 10.1007/s10955-010-9956-1
--
-- The three criteria are not identified.  They are represented by their
-- different neighbourhood majorants.  A criterion with a smaller majorant has
-- a larger admissible activity region.  This module proves only the valid
-- direction of implication, preventing a sharper Fernández--Procacci or
-- interpolating witness from being silently relabelled as Kotecký--Preiss.
------------------------------------------------------------------------

record PolymerCriterionComparison (Polymer : Set) : Set₁ where
  field
    activity budget : Polymer → ℚ

    -- KP uses the exponential of the full incompatible-neighbourhood sum.
    kpExponentialMajorant : Polymer → ℚ

    -- Fernández--Procacci replaces that exponential by the compatible-subset
    -- partition function of the incompatibility neighbourhood.
    fernandezProcacciMajorant : Polymer → ℚ

    -- The Bissacot--Fernández--Procacci comparison permits an interpolating or
    -- otherwise improved neighbourhood majorant.  Its exact physical instance
    -- must say which incompatibility family is being summed over.
    interpolatingMajorant : Polymer → ℚ

    -- Sign convention: activities are absolute activities and hence
    -- nonnegative.  Monotonicity of multiplication is recorded only in this
    -- nonnegative activity slot; no invalid multiplication of inequalities by
    -- an arbitrary rational is permitted.
    activityNonnegative : ∀ polymer → 0ℚ ≤ activity polymer
    activityTimesMonotone : ∀ polymer {left right} →
      left ≤ right →
      activity polymer * left ≤ activity polymer * right

    transitive : ∀ {left middle right} →
      left ≤ middle → middle ≤ right → left ≤ right

    fernandezProcacciBelowKP : ∀ polymer →
      fernandezProcacciMajorant polymer ≤ kpExponentialMajorant polymer

    interpolatingBelowFernandezProcacci : ∀ polymer →
      interpolatingMajorant polymer ≤ fernandezProcacciMajorant polymer

open PolymerCriterionComparison public

KoteckyPreissCriterion : ∀ {Polymer} →
  PolymerCriterionComparison Polymer → Set
KoteckyPreissCriterion dataSet = ∀ polymer →
  activity dataSet polymer * kpExponentialMajorant dataSet polymer
  ≤ budget dataSet polymer

FernandezProcacciCriterion : ∀ {Polymer} →
  PolymerCriterionComparison Polymer → Set
FernandezProcacciCriterion dataSet = ∀ polymer →
  activity dataSet polymer * fernandezProcacciMajorant dataSet polymer
  ≤ budget dataSet polymer

InterpolatingCriterion : ∀ {Polymer} →
  PolymerCriterionComparison Polymer → Set
InterpolatingCriterion dataSet = ∀ polymer →
  activity dataSet polymer * interpolatingMajorant dataSet polymer
  ≤ budget dataSet polymer

koteckyPreissImpliesFernandezProcacci :
  ∀ {Polymer} (dataSet : PolymerCriterionComparison Polymer) →
  KoteckyPreissCriterion dataSet →
  FernandezProcacciCriterion dataSet
koteckyPreissImpliesFernandezProcacci dataSet kp polymer =
  transitive dataSet
    (activityTimesMonotone dataSet polymer
      (fernandezProcacciBelowKP dataSet polymer))
    (kp polymer)

fernandezProcacciImpliesInterpolating :
  ∀ {Polymer} (dataSet : PolymerCriterionComparison Polymer) →
  FernandezProcacciCriterion dataSet →
  InterpolatingCriterion dataSet
fernandezProcacciImpliesInterpolating dataSet fp polymer =
  transitive dataSet
    (activityTimesMonotone dataSet polymer
      (interpolatingBelowFernandezProcacci dataSet polymer))
    (fp polymer)

koteckyPreissImpliesInterpolating :
  ∀ {Polymer} (dataSet : PolymerCriterionComparison Polymer) →
  KoteckyPreissCriterion dataSet →
  InterpolatingCriterion dataSet
koteckyPreissImpliesInterpolating dataSet kp =
  fernandezProcacciImpliesInterpolating dataSet
    (koteckyPreissImpliesFernandezProcacci dataSet kp)

record StrictCriterionSlack
    {Polymer : Set}
    (dataSet : PolymerCriterionComparison Polymer) : Set₁ where
  field
    witnessPolymer : Polymer
    StrictlyLess : ℚ → ℚ → Set
    fpStrictlyBelowKP :
      StrictlyLess
        (fernandezProcacciMajorant dataSet witnessPolymer)
        (kpExponentialMajorant dataSet witnessPolymer)
    interpolatingStrictlyBelowFP :
      StrictlyLess
        (interpolatingMajorant dataSet witnessPolymer)
        (fernandezProcacciMajorant dataSet witnessPolymer)

open StrictCriterionSlack public

kpToFernandezProcacciDominanceLevel : ProofLevel
kpToFernandezProcacciDominanceLevel = machineChecked

fernandezProcacciToInterpolatingDominanceLevel : ProofLevel
fernandezProcacciToInterpolatingDominanceLevel = machineChecked

polymerCriterionSignConventionLevel : ProofLevel
polymerCriterionSignConventionLevel = machineChecked

-- Strict improvement is model dependent: it requires an actual incompatibility
-- neighbourhood whose compatible-subset partition function is strictly smaller
-- than the KP exponential majorant.  It is not inferred from names alone.
physicalStrictCriterionSlackLevel : ProofLevel
physicalStrictCriterionSlackLevel = conditional
