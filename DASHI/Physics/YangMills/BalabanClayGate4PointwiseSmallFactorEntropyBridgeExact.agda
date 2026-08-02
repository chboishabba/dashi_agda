module DASHI.Physics.YangMills.BalabanClayGate4PointwiseSmallFactorEntropyBridgeExact where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat)
open import Relation.Binary.PropositionalEquality using (subst; sym)

open import DASHI.Physics.YangMills.CompactLieProofLevel

------------------------------------------------------------------------
-- Pointwise R-operation small factors versus polymer entropy.
--
-- Tadeusz Bałaban,
-- "Large Field Renormalization I: The Basic Step of the R-Operation",
-- Communications in Mathematical Physics 122 (1989), 175--202.
-- DOI: 10.1007/BF01257412.
--
-- Tadeusz Bałaban,
-- "Large Field Renormalization II: Localization, Exponentiation, and Bounds
-- for the R-Operation", Communications in Mathematical Physics 122 (1989),
-- 355--392. DOI: 10.1007/BF01238433.
--
-- Roman Kotecký and David Preiss,
-- "Cluster Expansion for Abstract Polymer Models",
-- Communications in Mathematical Physics 103 (1986), 491--498.
-- DOI: 10.1007/BF01211762.
--
-- The source small factor and the animal-count weight are separate. Their
-- product is assembled before the strict convergence-ratio check. The power
-- operation and its product law belong to the scalar backend; this bridge does
-- not attempt to reconstruct a commutative monoid from insufficient laws.
------------------------------------------------------------------------

record MultiplicativeSuppressionAlgebra (Bound : Set) : Set₁ where
  field
    one : Bound
    multiply : Bound → Bound → Bound
    power : Bound → Nat → Bound
    LessEqual StrictlyLess : Bound → Bound → Set

    reflexive : ∀ value → LessEqual value value
    transitive : ∀ {left middle right} →
      LessEqual left middle → LessEqual middle right → LessEqual left right

    multiplyMonotone : ∀ {left leftUpper right rightUpper} →
      LessEqual left leftUpper → LessEqual right rightUpper →
      LessEqual (multiply left right) (multiply leftUpper rightUpper)

    powerProduct : ∀ left right exponent →
      multiply (power left exponent) (power right exponent)
      ≡ power (multiply left right) exponent

open MultiplicativeSuppressionAlgebra public

record PointwiseSmallFactorComponent
    {Component Bound : Set}
    (algebra : MultiplicativeSuppressionAlgebra Bound) : Set₁ where
  field
    component : Component
    componentSize : Nat

    sourceSmallFactor entropyFactor : Bound
    sourceActivity animalMultiplicityWeight combinedWeight : Bound

    sourceActivitySuppressed :
      LessEqual algebra sourceActivity
        (power algebra sourceSmallFactor componentSize)

    animalWeightBounded :
      LessEqual algebra animalMultiplicityWeight
        (power algebra entropyFactor componentSize)

    combinedWeightMeaning :
      combinedWeight
      ≡ multiply algebra sourceActivity animalMultiplicityWeight

open PointwiseSmallFactorComponent public

combinedComponentWeightBound :
  ∀ {Component Bound}
    {algebra : MultiplicativeSuppressionAlgebra Bound} →
  (dataSet : PointwiseSmallFactorComponent {Component} algebra) →
  LessEqual algebra
    (combinedWeight dataSet)
    (power algebra
      (multiply algebra
        (sourceSmallFactor dataSet)
        (entropyFactor dataSet))
      (componentSize dataSet))
combinedComponentWeightBound {algebra = algebra} dataSet =
  subst
    (λ lower → LessEqual algebra lower
      (power algebra
        (multiply algebra
          (sourceSmallFactor dataSet)
          (entropyFactor dataSet))
        (componentSize dataSet)))
    (sym (combinedWeightMeaning dataSet))
    (subst
      (λ upper → LessEqual algebra
        (multiply algebra
          (sourceActivity dataSet)
          (animalMultiplicityWeight dataSet))
        upper)
      (powerProduct algebra
        (sourceSmallFactor dataSet)
        (entropyFactor dataSet)
        (componentSize dataSet))
      (multiplyMonotone algebra
        (sourceActivitySuppressed dataSet)
        (animalWeightBounded dataSet)))

record PointwiseEntropyConvergence
    {Bound : Set} (algebra : MultiplicativeSuppressionAlgebra Bound) : Set₁ where
  field
    sourceSmallFactor entropyFactor decayWeight : Bound
    weightedRatio : Bound

    weightedRatioMeaning :
      weightedRatio
      ≡ multiply algebra
          (multiply algebra sourceSmallFactor entropyFactor)
          decayWeight

    weightedRatioBelowOne :
      StrictlyLess algebra weightedRatio (one algebra)

open PointwiseEntropyConvergence public

pointwiseSmallFactorEntropyAssemblyLevel : ProofLevel
pointwiseSmallFactorEntropyAssemblyLevel = machineChecked

physicalPointwiseSmallFactorInputsLevel : ProofLevel
physicalPointwiseSmallFactorInputsLevel = conditional

physicalAnimalEntropyRatioInputsLevel : ProofLevel
physicalAnimalEntropyRatioInputsLevel = conditional
