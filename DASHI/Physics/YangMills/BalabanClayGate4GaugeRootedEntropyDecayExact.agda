module DASHI.Physics.YangMills.BalabanClayGate4GaugeRootedEntropyDecayExact where

open import Agda.Builtin.Nat using (Nat; zero; suc)

open import DASHI.Physics.YangMills.CompactLieProofLevel

------------------------------------------------------------------------
-- Rooted gauge-polymer entropy versus exponential decay.
--
-- Roman Kotecký and David Preiss,
-- "Cluster Expansion for Abstract Polymer Models",
-- Communications in Mathematical Physics 103 (1986), 491--498.
-- DOI: 10.1007/BF01211762.
--
-- Roberto Fernández and Aldo Procacci,
-- "Cluster Expansion for Abstract Polymer Models. New Bounds from an Old
-- Approach", Communications in Mathematical Physics 274 (2007), 123--140.
-- arXiv:math-ph/0605041. DOI: 10.1007/s00220-007-0279-2.
--
-- J. Dimock,
-- "The Renormalization Group According to Balaban III. Convergence",
-- Annales Henri Poincare 15 (11) (2014), 2133--2175.
-- arXiv:1304.0705v1. DOI: 10.1007/s00023-013-0303-3.
--
-- If the number of rooted polymers of size m grows like C_ent^m and every
-- activity decays like exp(-mu m), then the combined shell ratio is
-- C_ent exp(-(mu-kappa)).  This module performs the finite geometric summation.
-- A physical proof supplies the shell majorant and one uniform bound on all
-- partial geometric sums.
------------------------------------------------------------------------

record OrderedGeometricSum (Scalar : Set) : Set₁ where
  field
    zero one : Scalar
    add multiply : Scalar → Scalar → Scalar
    LessEqual : Scalar → Scalar → Set

    reflexive : ∀ value → LessEqual value value
    transitive : ∀ {left middle right} →
      LessEqual left middle → LessEqual middle right → LessEqual left right

    addMonotone : ∀ {left lower right upper} →
      LessEqual left lower → LessEqual right upper →
      LessEqual (add left right) (add lower upper)

    multiplyMonotone : ∀ {left lower right upper} →
      LessEqual left lower → LessEqual right upper →
      LessEqual (multiply left right) (multiply lower upper)

open OrderedGeometricSum public

power :
  ∀ {Scalar} → OrderedGeometricSum Scalar → Scalar → Nat → Scalar
power algebra ratio zero = one algebra
power algebra ratio (suc exponent) =
  multiply algebra ratio (power algebra ratio exponent)

geometricActivityMajorant :
  ∀ {Scalar} → OrderedGeometricSum Scalar →
  Scalar → Scalar → Nat → Scalar
geometricActivityMajorant algebra amplitude ratio zero = zero algebra
geometricActivityMajorant algebra amplitude ratio (suc depth) =
  add algebra
    (multiply algebra amplitude (power algebra ratio depth))
    (geometricActivityMajorant algebra amplitude ratio depth)

rootedShellPartialSum :
  ∀ {Scalar} → OrderedGeometricSum Scalar →
  (Nat → Scalar) → Nat → Scalar
rootedShellPartialSum algebra shell zero = zero algebra
rootedShellPartialSum algebra shell (suc depth) =
  add algebra (shell depth)
    (rootedShellPartialSum algebra shell depth)

record RootedEntropyDecayData (Scalar : Set) : Set₁ where
  field
    algebra : OrderedGeometricSum Scalar

    entropyBase decayAfterRootWeight combinedRatio amplitude : Scalar
    shellActivity : Nat → Scalar

    combinedRatioMeaning :
      combinedRatio
      ≡ multiply algebra entropyBase decayAfterRootWeight

    shellActivityBound : ∀ size →
      LessEqual algebra
        (shellActivity size)
        (multiply algebra amplitude (power algebra combinedRatio size))

open RootedEntropyDecayData public

rootedShellPartialSumBelowGeometricMajorant :
  ∀ {Scalar}
    (dataSet : RootedEntropyDecayData Scalar)
    depth →
  LessEqual (algebra dataSet)
    (rootedShellPartialSum (algebra dataSet)
      (shellActivity dataSet) depth)
    (geometricActivityMajorant (algebra dataSet)
      (amplitude dataSet) (combinedRatio dataSet) depth)
rootedShellPartialSumBelowGeometricMajorant dataSet zero =
  reflexive (algebra dataSet) (zero (algebra dataSet))
rootedShellPartialSumBelowGeometricMajorant dataSet (suc depth) =
  addMonotone (algebra dataSet)
    (shellActivityBound dataSet depth)
    (rootedShellPartialSumBelowGeometricMajorant dataSet depth)

record UniformRootedGeometricSummability
    {Scalar : Set}
    (dataSet : RootedEntropyDecayData Scalar) : Set₁ where
  field
    rootedAllowance : Scalar
    combinedRatioBelowOne : Set

    everyPartialMajorantBelowAllowance : ∀ depth →
      LessEqual (algebra dataSet)
        (geometricActivityMajorant (algebra dataSet)
          (amplitude dataSet) (combinedRatio dataSet) depth)
        rootedAllowance

open UniformRootedGeometricSummability public

allFiniteRootedShellSumsBelowAllowance :
  ∀ {Scalar}
    {dataSet : RootedEntropyDecayData Scalar} →
  (summability : UniformRootedGeometricSummability dataSet) →
  ∀ depth →
  LessEqual (algebra dataSet)
    (rootedShellPartialSum (algebra dataSet)
      (shellActivity dataSet) depth)
    (rootedAllowance summability)
allFiniteRootedShellSumsBelowAllowance {dataSet = dataSet}
    summability depth =
  transitive (algebra dataSet)
    (rootedShellPartialSumBelowGeometricMajorant dataSet depth)
    (everyPartialMajorantBelowAllowance summability depth)

gaugeRootedEntropyDecayFiniteLevel : ProofLevel
gaugeRootedEntropyDecayFiniteLevel = machineChecked

gaugeRootedGeometricSummabilityLevel : ProofLevel
gaugeRootedGeometricSummabilityLevel = machineChecked

koteckyPreissRootedCriterionSourceLevel : ProofLevel
koteckyPreissRootedCriterionSourceLevel = standardImported

fernandezProcacciImprovedCriterionSourceLevel : ProofLevel
fernandezProcacciImprovedCriterionSourceLevel = standardImported

physicalGaugePolymerEntropyCountInputsLevel : ProofLevel
physicalGaugePolymerEntropyCountInputsLevel = conditional

physicalGaugeActivityExponentialDecayInputsLevel : ProofLevel
physicalGaugeActivityExponentialDecayInputsLevel = conditional
