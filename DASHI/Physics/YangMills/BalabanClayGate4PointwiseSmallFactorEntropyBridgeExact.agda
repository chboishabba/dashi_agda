module DASHI.Physics.YangMills.BalabanClayGate4PointwiseSmallFactorEntropyBridgeExact where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat; zero; suc)
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
-- The source small factor and the animal-count weight are separate.  Their
-- product is assembled before the strict convergence-ratio check.
------------------------------------------------------------------------

record MultiplicativeSuppressionAlgebra (Bound : Set) : Set₁ where
  field
    one : Bound
    multiply : Bound → Bound → Bound
    LessEqual StrictlyLess : Bound → Bound → Set

    reflexive : ∀ value → LessEqual value value
    transitive : ∀ {left middle right} →
      LessEqual left middle → LessEqual middle right → LessEqual left right

    multiplyMonotone : ∀ {left leftUpper right rightUpper} →
      LessEqual left leftUpper → LessEqual right rightUpper →
      LessEqual (multiply left right) (multiply leftUpper rightUpper)

    multiplyAssociative : ∀ left middle right →
      multiply (multiply left middle) right
      ≡ multiply left (multiply middle right)

    multiplyCommutative : ∀ left right →
      multiply left right ≡ multiply right left

open MultiplicativeSuppressionAlgebra public

power :
  ∀ {Bound} → MultiplicativeSuppressionAlgebra Bound → Bound → Nat → Bound
power algebra ratio zero = one algebra
power algebra ratio (suc exponent) =
  multiply algebra ratio (power algebra ratio exponent)

powerProduct :
  ∀ {Bound}
    (algebra : MultiplicativeSuppressionAlgebra Bound)
    left right exponent →
  multiply algebra
    (power algebra left exponent)
    (power algebra right exponent)
  ≡ power algebra (multiply algebra left right) exponent
powerProduct algebra left right zero =
  multiplyCommutative algebra (one algebra) (one algebra)
powerProduct algebra left right (suc exponent) =
  let induction = powerProduct algebra left right exponent
  in
  subst
    (λ selected →
      multiply algebra
        (multiply algebra left (power algebra left exponent))
        (multiply algebra right (power algebra right exponent))
      ≡ multiply algebra (multiply algebra left right) selected)
    induction
    (subst
      (λ selected →
        multiply algebra
          (multiply algebra left (power algebra left exponent))
          (multiply algebra right (power algebra right exponent))
        ≡ selected)
      (sym (multiplyAssociative algebra
        (multiply algebra left right)
        (power algebra left exponent)
        (power algebra right exponent)))
      (subst
        (λ selected →
          multiply algebra
            (multiply algebra left (power algebra left exponent))
            (multiply algebra right (power algebra right exponent))
          ≡ multiply algebra selected (power algebra right exponent))
        (subst
          (λ selected →
            multiply algebra left
              (multiply algebra (power algebra left exponent) right)
            ≡ multiply algebra selected (power algebra left exponent))
          (multiplyCommutative algebra left right)
          (subst
            (λ selected →
              multiply algebra
                (multiply algebra left (power algebra left exponent))
                (multiply algebra right (power algebra right exponent))
              ≡ multiply algebra left selected)
            (sym (multiplyAssociative algebra
              right (power algebra left exponent)
              (power algebra right exponent)))
            (subst
              (λ selected →
                multiply algebra
                  (multiply algebra left (power algebra left exponent))
                  (multiply algebra right (power algebra right exponent))
                ≡ selected)
              (sym (multiplyAssociative algebra
                left
                (multiply algebra (power algebra left exponent) right)
                (power algebra right exponent)))
              (subst
                (λ selected →
                  multiply algebra
                    (multiply algebra left (power algebra left exponent))
                    (multiply algebra right (power algebra right exponent))
                  ≡ multiply algebra
                      (multiply algebra left selected)
                      (power algebra right exponent))
                (multiplyCommutative algebra
                  (power algebra left exponent) right)
                (multiplyAssociative algebra
                  (multiply algebra left (power algebra left exponent))
                  right
                  (power algebra right exponent)))))))))

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
