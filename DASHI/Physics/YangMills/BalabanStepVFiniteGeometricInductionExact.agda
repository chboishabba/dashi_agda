module DASHI.Physics.YangMills.BalabanStepVFiniteGeometricInductionExact where

------------------------------------------------------------------------
-- PROVENANCE
--
-- Roman Kotecký and David Preiss,
-- "Cluster Expansion for Abstract Polymer Models",
-- Communications in Mathematical Physics 103 (1986), 491--498.
-- DOI: 10.1007/BF01211762.
--
-- PURPOSE
-- Prove the finite geometric estimate by induction inside the round-nine
-- ordered-semiring interface.  No completed infinite series is used.  The only
-- scalar-specific leaf is a supersolution B satisfying 1 + q B <= B, which on
-- an ordered field is supplied by B = (1-q)^(-1).
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl; cong; sym; trans)
open import Agda.Builtin.Nat using (zero; suc)
open import Relation.Binary.PropositionalEquality using (subst)

import DASHI.Physics.YangMills.BalabanStepVFiniteGeometricBackendExact as StepV
open import DASHI.Physics.YangMills.CompactLieProofLevel

record GeometricSemiringLaws
    {Scalar : Set}
    (kernel : StepV.OrderedSemiringKernel Scalar) : Set₁ where
  field
    addAssociative : ∀ left middle right →
      StepV.add kernel (StepV.add kernel left middle) right
      ≡ StepV.add kernel left (StepV.add kernel middle right)

    addIdentityLeft : ∀ value →
      StepV.add kernel (StepV.zero kernel) value ≡ value

    addIdentityRight : ∀ value →
      StepV.add kernel value (StepV.zero kernel) ≡ value

    multiplyZeroRight : ∀ value →
      StepV.multiply kernel value (StepV.zero kernel)
      ≡ StepV.zero kernel

    multiplyDistributesOverAddLeft : ∀ factor left right →
      StepV.multiply kernel factor (StepV.add kernel left right)
      ≡ StepV.add kernel
          (StepV.multiply kernel factor left)
          (StepV.multiply kernel factor right)

    zeroNonnegative :
      StepV.LessEqual kernel (StepV.zero kernel) (StepV.zero kernel)

    oneNonnegative :
      StepV.LessEqual kernel (StepV.zero kernel) (StepV.one kernel)

open GeometricSemiringLaws public

powerNonnegative :
  ∀ {Scalar}
    {kernel : StepV.OrderedSemiringKernel Scalar} →
  (laws : GeometricSemiringLaws kernel) →
  ∀ {ratio} →
  StepV.LessEqual kernel (StepV.zero kernel) ratio →
  ∀ exponent →
  StepV.LessEqual kernel
    (StepV.zero kernel)
    (StepV.power kernel ratio exponent)
powerNonnegative laws ratioNonnegative zero =
  oneNonnegative laws
powerNonnegative {kernel = kernel} laws ratioNonnegative (suc exponent) =
  subst
    (λ value →
      StepV.LessEqual kernel value
        (StepV.multiply kernel ratio
          (StepV.power kernel ratio exponent)))
    (multiplyZeroRight laws (StepV.zero kernel))
    (StepV.multiplyMonotoneNonnegative kernel
      (zeroNonnegative laws)
      (zeroNonnegative laws)
      ratioNonnegative
      (powerNonnegative laws ratioNonnegative exponent))

geometricPartialSumNonnegative :
  ∀ {Scalar}
    {kernel : StepV.OrderedSemiringKernel Scalar} →
  (laws : GeometricSemiringLaws kernel) →
  ∀ {ratio} →
  StepV.LessEqual kernel (StepV.zero kernel) ratio →
  ∀ count →
  StepV.LessEqual kernel
    (StepV.zero kernel)
    (StepV.geometricPartialSum kernel ratio count)
geometricPartialSumNonnegative laws ratioNonnegative zero =
  zeroNonnegative laws
geometricPartialSumNonnegative {kernel = kernel} laws ratioNonnegative (suc count) =
  subst
    (λ value →
      StepV.LessEqual kernel value
        (StepV.add kernel
          (StepV.geometricPartialSum kernel ratio count)
          (StepV.power kernel ratio count)))
    (addIdentityLeft laws (StepV.zero kernel))
    (StepV.addMonotone kernel
      (geometricPartialSumNonnegative laws ratioNonnegative count)
      (powerNonnegative laws ratioNonnegative count))

geometricPartialSumAffineRecurrence :
  ∀ {Scalar}
    {kernel : StepV.OrderedSemiringKernel Scalar} →
  (laws : GeometricSemiringLaws kernel) →
  ∀ ratio count →
  StepV.geometricPartialSum kernel ratio (suc count)
  ≡ StepV.add kernel
      (StepV.one kernel)
      (StepV.multiply kernel ratio
        (StepV.geometricPartialSum kernel ratio count))
geometricPartialSumAffineRecurrence {kernel = kernel} laws ratio zero =
  trans
    (addIdentityLeft laws (StepV.one kernel))
    (sym
      (trans
        (cong
          (StepV.add kernel (StepV.one kernel))
          (multiplyZeroRight laws ratio))
        (addIdentityRight laws (StepV.one kernel))))
geometricPartialSumAffineRecurrence {kernel = kernel} laws ratio (suc count) =
  let
    sum = StepV.geometricPartialSum kernel ratio count
    powerAt = StepV.power kernel ratio count
  in
  trans
    (cong
      (λ prefix →
        StepV.add kernel prefix
          (StepV.multiply kernel ratio powerAt))
      (geometricPartialSumAffineRecurrence laws ratio count))
    (trans
      (addAssociative laws
        (StepV.one kernel)
        (StepV.multiply kernel ratio sum)
        (StepV.multiply kernel ratio powerAt))
      (cong
        (StepV.add kernel (StepV.one kernel))
        (sym
          (multiplyDistributesOverAddLeft laws
            ratio sum powerAt))))

record FiniteGeometricSupersolution
    {Scalar : Set}
    (kernel : StepV.OrderedSemiringKernel Scalar)
    (laws : GeometricSemiringLaws kernel)
    (ratio : Scalar) : Set₁ where
  field
    ratioNonnegative :
      StepV.LessEqual kernel (StepV.zero kernel) ratio

    ratioBelowOne :
      StepV.StrictlyLess kernel ratio (StepV.one kernel)

    uniformBound : Scalar

    zeroBelowUniformBound :
      StepV.LessEqual kernel (StepV.zero kernel) uniformBound

    affineSupersolution :
      StepV.LessEqual kernel
        (StepV.add kernel
          (StepV.one kernel)
          (StepV.multiply kernel ratio uniformBound))
        uniformBound

open FiniteGeometricSupersolution public

allFiniteGeometricPartialSumsBounded :
  ∀ {Scalar}
    {kernel : StepV.OrderedSemiringKernel Scalar}
    {laws : GeometricSemiringLaws kernel}
    {ratio : Scalar} →
  (supersolution : FiniteGeometricSupersolution kernel laws ratio) →
  ∀ count →
  StepV.LessEqual kernel
    (StepV.geometricPartialSum kernel ratio count)
    (uniformBound supersolution)
allFiniteGeometricPartialSumsBounded supersolution zero =
  zeroBelowUniformBound supersolution
allFiniteGeometricPartialSumsBounded
    {kernel = kernel} {laws = laws} {ratio = ratio}
    supersolution (suc count) =
  subst
    (λ value →
      StepV.LessEqual kernel value
        (uniformBound supersolution))
    (sym (geometricPartialSumAffineRecurrence laws ratio count))
    (StepV.transitive kernel
      (StepV.addMonotone kernel
        (StepV.reflexive kernel (StepV.one kernel))
        (StepV.multiplyMonotoneNonnegative kernel
          (ratioNonnegative supersolution)
          (geometricPartialSumNonnegative laws
            (ratioNonnegative supersolution) count)
          (StepV.reflexive kernel ratio)
          (allFiniteGeometricPartialSumsBounded supersolution count)))
      (affineSupersolution supersolution))

finiteGeometricUniformBoundFromSupersolution :
  ∀ {Scalar}
    {kernel : StepV.OrderedSemiringKernel Scalar}
    {laws : GeometricSemiringLaws kernel}
    {ratio : Scalar} →
  FiniteGeometricSupersolution kernel laws ratio →
  StepV.FiniteGeometricUniformBound kernel ratio
finiteGeometricUniformBoundFromSupersolution supersolution = record
  { ratioNonnegative = ratioNonnegative supersolution
  ; ratioBelowOne = ratioBelowOne supersolution
  ; uniformBound = uniformBound supersolution
  ; allFinitePartialSumsBounded =
      allFiniteGeometricPartialSumsBounded supersolution
  }

finiteGeometricAffineRecurrenceLevel : ProofLevel
finiteGeometricAffineRecurrenceLevel = machineChecked

finiteGeometricInductionLevel : ProofLevel
finiteGeometricInductionLevel = machineChecked

finiteGeometricConcreteSupersolutionLevel : ProofLevel
finiteGeometricConcreteSupersolutionLevel = conditional
