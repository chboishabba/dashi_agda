module DASHI.Physics.YangMills.BalabanStepVFiniteGeometricBackendExact where

------------------------------------------------------------------------
-- PROVENANCE
--
-- Roman Kotecký and David Preiss,
-- "Cluster Expansion for Abstract Polymer Models",
-- Communications in Mathematical Physics 103 (1986), 491--498.
-- DOI: 10.1007/BF01211762.
--
-- PURPOSE
-- Step V only needs uniform bounds for all finite shell sums.  This module
-- therefore proves the finite recurrence internally and leaves completion to an
-- infinite series as an optional later consequence rather than a hidden input.
------------------------------------------------------------------------

open import Agda.Primitive using (lzero)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; suc)

open import DASHI.Physics.YangMills.CompactLieProofLevel

record OrderedSemiringKernel (Scalar : Set) : Set₁ where
  field
    zero one : Scalar
    add multiply : Scalar → Scalar → Scalar
    LessEqual StrictlyLess : Scalar → Scalar → Set

    reflexive : ∀ value → LessEqual value value
    transitive : ∀ {left middle right} →
      LessEqual left middle → LessEqual middle right →
      LessEqual left right

    addMonotone : ∀ {left leftUpper right rightUpper} →
      LessEqual left leftUpper → LessEqual right rightUpper →
      LessEqual (add left right) (add leftUpper rightUpper)

    multiplyMonotoneNonnegative : ∀ {left leftUpper right rightUpper} →
      LessEqual zero left → LessEqual zero right →
      LessEqual left leftUpper → LessEqual right rightUpper →
      LessEqual (multiply left right) (multiply leftUpper rightUpper)

open OrderedSemiringKernel public

power :
  ∀ {Scalar} → OrderedSemiringKernel Scalar → Scalar → Nat → Scalar
power kernel ratio 0 = one kernel
power kernel ratio (suc exponent) =
  multiply kernel ratio (power kernel ratio exponent)

geometricPartialSum :
  ∀ {Scalar} → OrderedSemiringKernel Scalar → Scalar → Nat → Scalar
geometricPartialSum kernel ratio 0 = zero kernel
geometricPartialSum kernel ratio (suc count) =
  add kernel
    (geometricPartialSum kernel ratio count)
    (power kernel ratio count)

geometricPartialSumZero :
  ∀ {Scalar} (kernel : OrderedSemiringKernel Scalar) ratio →
  geometricPartialSum kernel ratio 0 ≡ zero kernel
geometricPartialSumZero kernel ratio = refl

geometricPartialSumSuccessor :
  ∀ {Scalar} (kernel : OrderedSemiringKernel Scalar) ratio count →
  geometricPartialSum kernel ratio (suc count)
  ≡ add kernel
      (geometricPartialSum kernel ratio count)
      (power kernel ratio count)
geometricPartialSumSuccessor kernel ratio count = refl

record FiniteGeometricUniformBound
    {Scalar : Set}
    (kernel : OrderedSemiringKernel Scalar)
    (ratio : Scalar) : Set₁ where
  field
    ratioNonnegative : LessEqual kernel (zero kernel) ratio
    ratioBelowOne : StrictlyLess kernel ratio (one kernel)

    uniformBound : Scalar
    allFinitePartialSumsBounded : ∀ count →
      LessEqual kernel
        (geometricPartialSum kernel ratio count)
        uniformBound

open FiniteGeometricUniformBound public

record PolynomiallyWeightedGeometricBound
    {Scalar : Set}
    (kernel : OrderedSemiringKernel Scalar)
    (ratio : Scalar)
    (polynomialDegree : Nat) : Set₁ where
  field
    natural : Nat → Scalar
    naturalPower : Nat → Nat → Scalar

    weightedTerm : Nat → Scalar
    weightedTermDefinition : ∀ index →
      weightedTerm index
      ≡ multiply kernel
          (naturalPower index polynomialDegree)
          (power kernel ratio index)

    weightedPartialSum : Nat → Scalar
    weightedPartialSumDefinition : ∀ count →
      weightedPartialSum (suc count)
      ≡ add kernel (weightedPartialSum count) (weightedTerm count)

    uniformWeightedBound : Scalar
    allFiniteWeightedSumsBounded : ∀ count →
      LessEqual kernel
        (weightedPartialSum count)
        uniformWeightedBound

    chosenLargerRatio : Scalar
    ratioBelowLargerRatio :
      StrictlyLess kernel ratio chosenLargerRatio
    largerRatioBelowOne :
      StrictlyLess kernel chosenLargerRatio (one kernel)

    eventualPolynomialAbsorption : Set
    eventualPolynomialAbsorptionEvidence :
      eventualPolynomialAbsorption

open PolynomiallyWeightedGeometricBound public

record StepVScalarBackend (Scalar : Set) : Set₁ where
  field
    kernel : OrderedSemiringKernel Scalar

    logarithm exponential expNegative : Scalar → Scalar
    fromNat : Nat → Scalar

    expPositive : Set
    expPositiveEvidence : expPositive

    expMonotone : Set
    expMonotoneEvidence : expMonotone

    expAdditiveMultiplicative : Set
    expAdditiveMultiplicativeEvidence :
      expAdditiveMultiplicative

    expNegativeIsInverse : Set
    expNegativeIsInverseEvidence : expNegativeIsInverse

    logPositiveDomain : Set
    logPositiveDomainEvidence : logPositiveDomain

    logarithmMonotone : Set
    logarithmMonotoneEvidence : logarithmMonotone

    logarithmExponentialInverse : Set
    logarithmExponentialInverseEvidence :
      logarithmExponentialInverse

    logMarginImpliesWeightedRatioBelowOne :
      ∀ animalConstant kappa →
      StrictlyLess kernel
        (logarithm (fromNat animalConstant)) kappa →
      StrictlyLess kernel
        (multiply kernel
          (fromNat animalConstant)
          (expNegative kappa))
        (one kernel)

open StepVScalarBackend public

record CompleteStepVFiniteSumBackend
    (Scalar : Set)
    (backend : StepVScalarBackend Scalar) : Set₁ where
  field
    animalConstant : Nat
    kappa : Scalar
    logarithmicMargin :
      StrictlyLess (kernel backend)
        (logarithm backend (fromNat backend animalConstant))
        kappa

    weightedRatio : Scalar
    weightedRatioDefinition :
      weightedRatio
      ≡ multiply (kernel backend)
          (fromNat backend animalConstant)
          (expNegative backend kappa)

    finiteGeometricBound :
      FiniteGeometricUniformBound (kernel backend) weightedRatio

    polynomialDegree : Nat
    polynomialWeightedBound :
      PolynomiallyWeightedGeometricBound
        (kernel backend) weightedRatio polynomialDegree

open CompleteStepVFiniteSumBackend public

weightedRatioBelowOne :
  ∀ {Scalar}
    {backend : StepVScalarBackend Scalar} →
  (complete : CompleteStepVFiniteSumBackend Scalar backend) →
  StrictlyLess (kernel backend)
    (weightedRatio complete)
    (one (kernel backend))
weightedRatioBelowOne {backend = backend} complete
  rewrite weightedRatioDefinition complete =
  logMarginImpliesWeightedRatioBelowOne backend
    (animalConstant complete)
    (kappa complete)
    (logarithmicMargin complete)

finiteGeometricDefinitionsLevel : ProofLevel
finiteGeometricDefinitionsLevel = machineChecked

logMarginWeightedRatioReducerLevel : ProofLevel
logMarginWeightedRatioReducerLevel = machineChecked

physicalStepVLogExpLawsLevel : ProofLevel
physicalStepVLogExpLawsLevel = conditional

finiteGeometricUniformBoundLevel : ProofLevel
finiteGeometricUniformBoundLevel = conditional

polynomialWeightedGeometricBoundLevel : ProofLevel
polynomialWeightedGeometricBoundLevel = conditional
