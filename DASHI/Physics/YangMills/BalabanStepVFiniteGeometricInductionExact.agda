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
-- ordered-semiring interface.  Equality laws are setoid-valued, so the theorem
-- applies directly to Bishop reals.  No completed infinite series is used.  The
-- only scalar-specific leaf is a supersolution B with 1 + q B <= B.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (zero; suc)

import DASHI.Physics.YangMills.BalabanStepVFiniteGeometricBackendExact as StepV
open import DASHI.Physics.YangMills.CompactLieProofLevel

record GeometricSemiringLaws
    {Scalar : Set}
    (kernel : StepV.OrderedSemiringKernel Scalar) : Set₁ where
  field
    Equivalent : Scalar → Scalar → Set

    equivalentRefl : ∀ value → Equivalent value value
    equivalentSym : ∀ {left right} →
      Equivalent left right → Equivalent right left
    equivalentTrans : ∀ {left middle right} →
      Equivalent left middle → Equivalent middle right →
      Equivalent left right

    lessEqualRespectLeft : ∀ {desired current upper} →
      Equivalent desired current →
      StepV.LessEqual kernel current upper →
      StepV.LessEqual kernel desired upper

    addCongruent : ∀ {left left′ right right′} →
      Equivalent left left′ → Equivalent right right′ →
      Equivalent
        (StepV.add kernel left right)
        (StepV.add kernel left′ right′)

    multiplyCongruent : ∀ {left left′ right right′} →
      Equivalent left left′ → Equivalent right right′ →
      Equivalent
        (StepV.multiply kernel left right)
        (StepV.multiply kernel left′ right′)

    addAssociative : ∀ left middle right →
      Equivalent
        (StepV.add kernel (StepV.add kernel left middle) right)
        (StepV.add kernel left (StepV.add kernel middle right))

    addIdentityLeft : ∀ value →
      Equivalent (StepV.add kernel (StepV.zero kernel) value) value

    addIdentityRight : ∀ value →
      Equivalent (StepV.add kernel value (StepV.zero kernel)) value

    multiplyZeroRight : ∀ value →
      Equivalent
        (StepV.multiply kernel value (StepV.zero kernel))
        (StepV.zero kernel)

    multiplyDistributesOverAddLeft : ∀ factor left right →
      Equivalent
        (StepV.multiply kernel factor (StepV.add kernel left right))
        (StepV.add kernel
          (StepV.multiply kernel factor left)
          (StepV.multiply kernel factor right))

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
  lessEqualRespectLeft laws
    (equivalentSym laws
      (multiplyZeroRight laws (StepV.zero kernel)))
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
  lessEqualRespectLeft laws
    (equivalentSym laws
      (addIdentityLeft laws (StepV.zero kernel)))
    (StepV.addMonotone kernel
      (geometricPartialSumNonnegative laws ratioNonnegative count)
      (powerNonnegative laws ratioNonnegative count))

geometricPartialSumAffineRecurrence :
  ∀ {Scalar}
    {kernel : StepV.OrderedSemiringKernel Scalar} →
  (laws : GeometricSemiringLaws kernel) →
  ∀ ratio count →
  Equivalent laws
    (StepV.geometricPartialSum kernel ratio (suc count))
    (StepV.add kernel
      (StepV.one kernel)
      (StepV.multiply kernel ratio
        (StepV.geometricPartialSum kernel ratio count)))
geometricPartialSumAffineRecurrence {kernel = kernel} laws ratio zero =
  equivalentTrans laws
    (addIdentityLeft laws (StepV.one kernel))
    (equivalentSym laws
      (equivalentTrans laws
        (addCongruent laws
          (equivalentRefl laws (StepV.one kernel))
          (multiplyZeroRight laws ratio))
        (addIdentityRight laws (StepV.one kernel))))
geometricPartialSumAffineRecurrence {kernel = kernel} laws ratio (suc count) =
  let
    sum = StepV.geometricPartialSum kernel ratio count
    powerAt = StepV.power kernel ratio count
  in
  equivalentTrans laws
    (addCongruent laws
      (geometricPartialSumAffineRecurrence laws ratio count)
      (equivalentRefl laws
        (StepV.multiply kernel ratio powerAt)))
    (equivalentTrans laws
      (addAssociative laws
        (StepV.one kernel)
        (StepV.multiply kernel ratio sum)
        (StepV.multiply kernel ratio powerAt))
      (addCongruent laws
        (equivalentRefl laws (StepV.one kernel))
        (equivalentSym laws
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
  lessEqualRespectLeft laws
    (geometricPartialSumAffineRecurrence laws ratio count)
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
