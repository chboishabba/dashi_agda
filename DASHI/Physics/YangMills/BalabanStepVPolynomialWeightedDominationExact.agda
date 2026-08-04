module DASHI.Physics.YangMills.BalabanStepVPolynomialWeightedDominationExact where

------------------------------------------------------------------------
-- PROVENANCE
--
-- Roman Kotecký and David Preiss,
-- "Cluster Expansion for Abstract Polymer Models",
-- Communications in Mathematical Physics 103 (1986), 491--498.
-- DOI: 10.1007/BF01211762.
--
-- PURPOSE
-- Reduce the polynomially weighted Step-V shell sum to one pointwise geometric
-- domination.  If n^p q^n <= M (q')^n for every n and q' has a finite
-- geometric bound, induction gives a uniform bound for every finite weighted
-- partial sum.  A later finite-prefix/eventual-tail theorem need only construct
-- M and q'; it does not need to reprove finite summation.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)

import DASHI.Physics.YangMills.BalabanStepVFiniteGeometricBackendExact as StepV
import DASHI.Physics.YangMills.BalabanStepVFiniteGeometricInductionExact as Geometric
open import DASHI.Physics.YangMills.CompactLieProofLevel

weightedPartialSum :
  ∀ {Scalar}
    (kernel : StepV.OrderedSemiringKernel Scalar) →
  (weightedTerm : Nat → Scalar) →
  Nat → Scalar
weightedPartialSum kernel weightedTerm zero = StepV.zero kernel
weightedPartialSum kernel weightedTerm (suc count) =
  StepV.add kernel
    (weightedPartialSum kernel weightedTerm count)
    (weightedTerm count)

weightedPartialSumZero :
  ∀ {Scalar}
    (kernel : StepV.OrderedSemiringKernel Scalar)
    weightedTerm →
  weightedPartialSum kernel weightedTerm zero ≡ StepV.zero kernel
weightedPartialSumZero kernel weightedTerm = refl

weightedPartialSumSuccessor :
  ∀ {Scalar}
    (kernel : StepV.OrderedSemiringKernel Scalar)
    weightedTerm count →
  weightedPartialSum kernel weightedTerm (suc count)
  ≡ StepV.add kernel
      (weightedPartialSum kernel weightedTerm count)
      (weightedTerm count)
weightedPartialSumSuccessor kernel weightedTerm count = refl

record PolynomialGeometricDomination
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

    pointwisePolynomialGeometricDomination : ∀ index →
      StepV.LessEqual kernel
        (weightedTerm index)
        (StepV.multiply kernel
          dominationConstant
          (StepV.power kernel chosenLargerRatio index))

open PolynomialGeometricDomination public

weightedPartialSumNonnegative :
  ∀ {Scalar}
    {kernel : StepV.OrderedSemiringKernel Scalar}
    {laws : Geometric.GeometricSemiringLaws kernel}
    {ratio polynomialDegree}
    (inputs : PolynomialGeometricDomination
      kernel laws ratio polynomialDegree) →
  ∀ count →
  StepV.LessEqual kernel
    (StepV.zero kernel)
    (weightedPartialSum kernel (weightedTerm inputs) count)
weightedPartialSumNonnegative inputs zero =
  Geometric.zeroNonnegative _
weightedPartialSumNonnegative
    {kernel = kernel} {laws = laws} inputs (suc count) =
  Geometric.lessEqualRespectLeft laws
    (Geometric.equivalentSym laws
      (Geometric.addIdentityLeft laws (StepV.zero kernel)))
    (StepV.addMonotone kernel
      (weightedPartialSumNonnegative inputs count)
      (weightedTermNonnegative inputs count))

weightedPartialSumDominatedByScaledGeometric :
  ∀ {Scalar}
    {kernel : StepV.OrderedSemiringKernel Scalar}
    {laws : Geometric.GeometricSemiringLaws kernel}
    {ratio polynomialDegree}
    (inputs : PolynomialGeometricDomination
      kernel laws ratio polynomialDegree) →
  ∀ count →
  StepV.LessEqual kernel
    (weightedPartialSum kernel (weightedTerm inputs) count)
    (StepV.multiply kernel
      (dominationConstant inputs)
      (StepV.geometricPartialSum kernel
        (chosenLargerRatio inputs) count))
weightedPartialSumDominatedByScaledGeometric
    {kernel = kernel} {laws = laws} inputs zero =
  Geometric.lessEqualRespectLeft laws
    (Geometric.equivalentRefl laws (StepV.zero kernel))
    (Geometric.lessEqualRespectLeft laws
      (Geometric.equivalentSym laws
        (Geometric.multiplyZeroRight laws
          (dominationConstant inputs)))
      (Geometric.zeroNonnegative laws))
weightedPartialSumDominatedByScaledGeometric
    {kernel = kernel} {laws = laws} inputs (suc count) =
  let
    q′ = chosenLargerRatio inputs
    constant = dominationConstant inputs
    oldSum = weightedPartialSum kernel (weightedTerm inputs) count
    oldGeometric = StepV.geometricPartialSum kernel q′ count
    newPower = StepV.power kernel q′ count

    summedBound :
      StepV.LessEqual kernel
        (StepV.add kernel oldSum (weightedTerm inputs count))
        (StepV.add kernel
          (StepV.multiply kernel constant oldGeometric)
          (StepV.multiply kernel constant newPower))
    summedBound =
      StepV.addMonotone kernel
        (weightedPartialSumDominatedByScaledGeometric inputs count)
        (pointwisePolynomialGeometricDomination inputs count)

    distributed :
      Geometric.Equivalent laws
        (StepV.multiply kernel constant
          (StepV.add kernel oldGeometric newPower))
        (StepV.add kernel
          (StepV.multiply kernel constant oldGeometric)
          (StepV.multiply kernel constant newPower))
    distributed =
      Geometric.multiplyDistributesOverAddLeft laws
        constant oldGeometric newPower
  in
  Geometric.lessEqualRespectLeft laws
    (Geometric.equivalentSym laws distributed)
    summedBound

allFinitePolynomialWeightedSumsBounded :
  ∀ {Scalar}
    {kernel : StepV.OrderedSemiringKernel Scalar}
    {laws : Geometric.GeometricSemiringLaws kernel}
    {ratio polynomialDegree}
    (inputs : PolynomialGeometricDomination
      kernel laws ratio polynomialDegree) →
  ∀ count →
  StepV.LessEqual kernel
    (weightedPartialSum kernel (weightedTerm inputs) count)
    (StepV.multiply kernel
      (dominationConstant inputs)
      (StepV.uniformBound (largerRatioBound inputs)))
allFinitePolynomialWeightedSumsBounded
    {kernel = kernel} inputs count =
  StepV.transitive kernel
    (weightedPartialSumDominatedByScaledGeometric inputs count)
    (StepV.multiplyMonotoneNonnegative kernel
      (dominationConstantNonnegative inputs)
      (Geometric.geometricPartialSumNonnegative _
        (StepV.ratioNonnegative (largerRatioBound inputs)) count)
      (StepV.reflexive kernel (dominationConstant inputs))
      (StepV.allFinitePartialSumsBounded
        (largerRatioBound inputs) count))

polynomiallyWeightedGeometricBoundFromDomination :
  ∀ {Scalar}
    {kernel : StepV.OrderedSemiringKernel Scalar}
    {laws : Geometric.GeometricSemiringLaws kernel}
    {ratio polynomialDegree} →
  PolynomialGeometricDomination kernel laws ratio polynomialDegree →
  StepV.PolynomiallyWeightedGeometricBound
    kernel ratio polynomialDegree
polynomiallyWeightedGeometricBoundFromDomination inputs = record
  { natural = natural inputs
  ; naturalPower = naturalPower inputs
  ; weightedTerm = weightedTerm inputs
  ; weightedTermDefinition = weightedTermDefinition inputs
  ; weightedPartialSum =
      weightedPartialSum _ (weightedTerm inputs)
  ; weightedPartialSumDefinition = λ count →
      weightedPartialSum _ (weightedTerm inputs) count
      ≡ weightedPartialSum _ (weightedTerm inputs) count
  ; uniformWeightedBound =
      StepV.multiply _
        (dominationConstant inputs)
        (StepV.uniformBound (largerRatioBound inputs))
  ; allFiniteWeightedSumsBounded =
      allFinitePolynomialWeightedSumsBounded inputs
  ; chosenLargerRatio = chosenLargerRatio inputs
  ; ratioBelowLargerRatio = ratioBelowLargerRatio inputs
  ; largerRatioBelowOne =
      StepV.ratioBelowOne (largerRatioBound inputs)
  ; eventualPolynomialAbsorption =
      ∀ index →
      StepV.LessEqual _
        (weightedTerm inputs index)
        (StepV.multiply _
          (dominationConstant inputs)
          (StepV.power _ (chosenLargerRatio inputs) index))
  ; eventualPolynomialAbsorptionEvidence =
      pointwisePolynomialGeometricDomination inputs
  }

polynomialWeightedFiniteSummationLevel : ProofLevel
polynomialWeightedFiniteSummationLevel = machineChecked

polynomialGeometricPointwiseDominationLevel : ProofLevel
polynomialGeometricPointwiseDominationLevel = conditional
