module DASHI.Physics.YangMills.BalabanStepVPolynomialDirectRatioExact where

------------------------------------------------------------------------
-- PROVENANCE
--
-- Roman Kotecký and David Preiss,
-- "Cluster Expansion for Abstract Polymer Models",
-- Communications in Mathematical Physics 103 (1986), 491--498.
-- DOI: 10.1007/BF01211762.
--
-- PURPOSE
-- Remove logarithm/exponential infrastructure from the polynomial shell
-- argument.  A finite prefix and one successor-preservation inequality on the
-- tail suffice.  This module proves the induction that turns those local data
-- into the exact PolynomialPrefixTailDomination consumed by Step V.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)
open import Agda.Builtin.Sigma using (Σ; _,_)
open import Data.Nat.Base using (_<_; _≤_; z≤n; s≤s)
open import Data.Nat.Properties using (+-suc)
open import Relation.Binary.PropositionalEquality using (cong; subst; sym)

import DASHI.Physics.YangMills.BalabanStepVFiniteGeometricBackendExact as StepV
import DASHI.Physics.YangMills.BalabanStepVFiniteGeometricInductionExact as Geometric
import DASHI.Physics.YangMills.BalabanStepVPolynomialPrefixTailDominationExact as PrefixTail
open import DASHI.Physics.YangMills.CompactLieProofLevel

------------------------------------------------------------------------
-- Elementary natural-order infrastructure.  It is kept local so the physical
-- theorem spends no input on index arithmetic.
------------------------------------------------------------------------

left≤leftPlus : ∀ left right → left ≤ left + right
left≤leftPlus zero right = z≤n
left≤leftPlus (suc left) right = s≤s (left≤leftPlus left right)

differenceWitness :
  ∀ left right → left ≤ right →
  Σ Nat (λ offset → right ≡ left + offset)
differenceWitness zero right z≤n = right , refl
differenceWitness (suc left) (suc right) (s≤s left≤right)
  with differenceWitness left right left≤right
... | offset , equality = offset , cong suc equality

record PolynomialDirectRatioInputs
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

    -- This is the only tail seed.
    tailSeed :
      StepV.LessEqual kernel
        (weightedTerm transitionIndex)
        (StepV.multiply kernel
          dominationConstant
          (StepV.power kernel chosenLargerRatio transitionIndex))

    -- A direct ratio calculation supplies this field.  Analytically it is the
    -- statement that, beyond transitionIndex, multiplication by q'/q absorbs
    -- the polynomial successor factor.  No logarithm is mentioned.
    tailSuccessorPreservesDomination : ∀ index →
      transitionIndex ≤ index →
      StepV.LessEqual kernel
        (weightedTerm index)
        (StepV.multiply kernel
          dominationConstant
          (StepV.power kernel chosenLargerRatio index)) →
      StepV.LessEqual kernel
        (weightedTerm (suc index))
        (StepV.multiply kernel
          dominationConstant
          (StepV.power kernel chosenLargerRatio (suc index)))

open PolynomialDirectRatioInputs public

private
  TailBound :
    ∀ {Scalar}
      {kernel : StepV.OrderedSemiringKernel Scalar}
      {laws : Geometric.GeometricSemiringLaws kernel}
      {ratio polynomialDegree}
      (inputs : PolynomialDirectRatioInputs
        kernel laws ratio polynomialDegree) →
    Nat → Set
  TailBound {kernel = kernel} inputs index =
    StepV.LessEqual kernel
      (weightedTerm inputs index)
      (StepV.multiply kernel
        (dominationConstant inputs)
        (StepV.power kernel (chosenLargerRatio inputs) index))

tailBoundAtOffset :
  ∀ {Scalar}
    {kernel : StepV.OrderedSemiringKernel Scalar}
    {laws : Geometric.GeometricSemiringLaws kernel}
    {ratio polynomialDegree}
    (inputs : PolynomialDirectRatioInputs
      kernel laws ratio polynomialDegree) →
  ∀ offset →
  TailBound inputs (transitionIndex inputs + offset)
tailBoundAtOffset inputs zero = tailSeed inputs
tailBoundAtOffset inputs (suc offset) =
  subst (TailBound inputs)
    (sym (+-suc (transitionIndex inputs) offset))
    (tailSuccessorPreservesDomination inputs
      (transitionIndex inputs + offset)
      (left≤leftPlus (transitionIndex inputs) offset)
      (tailBoundAtOffset inputs offset))

eventualTailDominationFromDirectRatio :
  ∀ {Scalar}
    {kernel : StepV.OrderedSemiringKernel Scalar}
    {laws : Geometric.GeometricSemiringLaws kernel}
    {ratio polynomialDegree}
    (inputs : PolynomialDirectRatioInputs
      kernel laws ratio polynomialDegree) →
  ∀ index →
  transitionIndex inputs ≤ index →
  TailBound inputs index
eventualTailDominationFromDirectRatio inputs index transition≤index
  with differenceWitness (transitionIndex inputs) index transition≤index
... | offset , refl = tailBoundAtOffset inputs offset

polynomialPrefixTailFromDirectRatio :
  ∀ {Scalar}
    {kernel : StepV.OrderedSemiringKernel Scalar}
    {laws : Geometric.GeometricSemiringLaws kernel}
    {ratio polynomialDegree} →
  PolynomialDirectRatioInputs kernel laws ratio polynomialDegree →
  PrefixTail.PolynomialPrefixTailDomination
    kernel laws ratio polynomialDegree
polynomialPrefixTailFromDirectRatio inputs = record
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
  ; transitionIndex = transitionIndex inputs
  ; finitePrefixDomination = finitePrefixDomination inputs
  ; eventualTailDomination =
      eventualTailDominationFromDirectRatio inputs
  }

polynomialWeightedBoundFromDirectRatio :
  ∀ {Scalar}
    {kernel : StepV.OrderedSemiringKernel Scalar}
    {laws : Geometric.GeometricSemiringLaws kernel}
    {ratio polynomialDegree} →
  PolynomialDirectRatioInputs kernel laws ratio polynomialDegree →
  StepV.PolynomiallyWeightedGeometricBound
    kernel ratio polynomialDegree
polynomialWeightedBoundFromDirectRatio inputs =
  PrefixTail.polynomialWeightedBoundFromPrefixTail
    (polynomialPrefixTailFromDirectRatio inputs)

directRatioTailInductionLevel : ProofLevel
directRatioTailInductionLevel = machineChecked

polynomialWeightedBoundFromDirectRatioLevel : ProofLevel
polynomialWeightedBoundFromDirectRatioLevel = machineChecked

physicalDirectRatioSuccessorInequalityLevel : ProofLevel
physicalDirectRatioSuccessorInequalityLevel = conditional
