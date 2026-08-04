module DASHI.Physics.YangMills.BalabanStepVPolynomialPrefixTailDominationExact where

------------------------------------------------------------------------
-- PROVENANCE
--
-- Roman Kotecký and David Preiss,
-- "Cluster Expansion for Abstract Polymer Models",
-- Communications in Mathematical Physics 103 (1986), 491--498.
-- DOI: 10.1007/BF01211762.
--
-- PURPOSE
-- Split the remaining pointwise polynomial domination into the exact two
-- arguments used in analysis: a finite startup range and an eventual tail.
-- Totality of natural-number order is proved here, so no physical input is
-- spent on deciding whether an index is before or after the transition.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Nat.Base using (_<_; _≤_; z≤n; s≤s)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)

import DASHI.Physics.YangMills.BalabanStepVFiniteGeometricBackendExact as StepV
import DASHI.Physics.YangMills.BalabanStepVFiniteGeometricInductionExact as Geometric
import DASHI.Physics.YangMills.BalabanStepVPolynomialWeightedDominationExact as Polynomial
open import DASHI.Physics.YangMills.CompactLieProofLevel

indexPrefixOrTail :
  ∀ (index transition : Nat) →
  (index < transition) ⊎ (transition ≤ index)
indexPrefixOrTail zero zero = inj₂ z≤n
indexPrefixOrTail zero (suc transition) = inj₁ (s≤s z≤n)
indexPrefixOrTail (suc index) zero = inj₂ z≤n
indexPrefixOrTail (suc index) (suc transition)
  with indexPrefixOrTail index transition
... | inj₁ prefix = inj₁ (s≤s prefix)
... | inj₂ tail = inj₂ (s≤s tail)

record PolynomialPrefixTailDomination
    {Scalar : Set}
    (kernel : StepV.OrderedSemiringKernel Scalar)
    (laws : Geometric.GeometricSemiringLaws kernel)
    (ratio : Scalar)
    (polynomialDegree : Nat) : Set₁ where
  field
    natural : Nat → Scalar
    naturalPower : Nat → Nat → Scalar

    weightedTerm : Nat → Scalar
    weightedTermDefinition : ∀ index →
      weightedTerm index
      ≡ StepV.multiply kernel
          (naturalPower index polynomialDegree)
          (StepV.power kernel ratio index)

    weightedTermNonnegative : ∀ index →
      StepV.LessEqual kernel
        (StepV.zero kernel)
        (weightedTerm index)

    chosenLargerRatio : Scalar
    ratioBelowLargerRatio :
      StepV.StrictlyLess kernel ratio chosenLargerRatio

    largerRatioBound :
      StepV.FiniteGeometricUniformBound kernel chosenLargerRatio

    dominationConstant : Scalar
    dominationConstantNonnegative :
      StepV.LessEqual kernel
        (StepV.zero kernel)
        dominationConstant

    transitionIndex : Nat

    finitePrefixDomination : ∀ index →
      index < transitionIndex →
      StepV.LessEqual kernel
        (weightedTerm index)
        (StepV.multiply kernel
          dominationConstant
          (StepV.power kernel chosenLargerRatio index))

    eventualTailDomination : ∀ index →
      transitionIndex ≤ index →
      StepV.LessEqual kernel
        (weightedTerm index)
        (StepV.multiply kernel
          dominationConstant
          (StepV.power kernel chosenLargerRatio index))

open PolynomialPrefixTailDomination public

allIndexPolynomialDomination :
  ∀ {Scalar}
    {kernel : StepV.OrderedSemiringKernel Scalar}
    {laws : Geometric.GeometricSemiringLaws kernel}
    {ratio polynomialDegree}
    (inputs : PolynomialPrefixTailDomination
      kernel laws ratio polynomialDegree) →
  ∀ index →
  StepV.LessEqual kernel
    (weightedTerm inputs index)
    (StepV.multiply kernel
      (dominationConstant inputs)
      (StepV.power kernel (chosenLargerRatio inputs) index))
allIndexPolynomialDomination inputs index
  with indexPrefixOrTail index (transitionIndex inputs)
... | inj₁ prefix = finitePrefixDomination inputs index prefix
... | inj₂ tail = eventualTailDomination inputs index tail

polynomialGeometricDominationFromPrefixTail :
  ∀ {Scalar}
    {kernel : StepV.OrderedSemiringKernel Scalar}
    {laws : Geometric.GeometricSemiringLaws kernel}
    {ratio polynomialDegree} →
  PolynomialPrefixTailDomination kernel laws ratio polynomialDegree →
  Polynomial.PolynomialGeometricDomination
    kernel laws ratio polynomialDegree
polynomialGeometricDominationFromPrefixTail inputs = record
  { natural = natural inputs
  ; naturalPower = naturalPower inputs
  ; weightedTerm = weightedTerm inputs
  ; weightedTermDefinition = weightedTermDefinition inputs
  ; weightedTermNonnegative = weightedTermNonnegative inputs
  ; chosenLargerRatio = chosenLargerRatio inputs
  ; ratioBelowLargerRatio = ratioBelowLargerRatio inputs
  ; largerRatioBound = largerRatioBound inputs
  ; dominationConstant = dominationConstant inputs
  ; dominationConstantNonnegative =
      dominationConstantNonnegative inputs
  ; pointwisePolynomialGeometricDomination =
      allIndexPolynomialDomination inputs
  }

polynomialWeightedBoundFromPrefixTail :
  ∀ {Scalar}
    {kernel : StepV.OrderedSemiringKernel Scalar}
    {laws : Geometric.GeometricSemiringLaws kernel}
    {ratio polynomialDegree} →
  PolynomialPrefixTailDomination kernel laws ratio polynomialDegree →
  StepV.PolynomiallyWeightedGeometricBound
    kernel ratio polynomialDegree
polynomialWeightedBoundFromPrefixTail inputs =
  Polynomial.polynomiallyWeightedGeometricBoundFromDomination
    (polynomialGeometricDominationFromPrefixTail inputs)

polynomialPrefixTailScaleSplitLevel : ProofLevel
polynomialPrefixTailScaleSplitLevel = machineChecked

polynomialPrefixTailDominationAssemblyLevel : ProofLevel
polynomialPrefixTailDominationAssemblyLevel = machineChecked

polynomialFinitePrefixAndEventualTailInputsLevel : ProofLevel
polynomialFinitePrefixAndEventualTailInputsLevel = conditional
