module DASHI.Physics.YangMills.BalabanClayGate4HRBetaHalfRemainderDominanceExact where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Relation.Binary.PropositionalEquality using (cong; subst; sym; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Physics.YangMills.BalabanClayGate4DyadicRunningCouplingConventionExact as Dyadic
import DASHI.Physics.YangMills.BalabanClayGate4PrimaryCouplingAdmissibilityInductionExact as Induction
import DASHI.Physics.YangMills.BalabanClayP3PhysicalOneStepTransferExact as P3
import DASHI.Physics.YangMills.BalabanClayT4RunningCouplingConventionBridgeExact as Running

------------------------------------------------------------------------
-- H-Rbeta half-remainder dominance.
--
-- Tadeusz Bałaban,
-- "Renormalization Group Approach to Lattice Gauge Field Theories. I.
-- Generation of Effective Actions in a Small Field Approximation and a
-- Coupling Constant Renormalization in Four Dimensions",
-- Communications in Mathematical Physics 109 (2) (1987), 249--301.
-- DOI: 10.1007/BF01215223.
--
-- If the inverse-coupling remainder obeys
--
--   |r_k| <= (1/2) Delta_k,
--
-- then ordered additive-group algebra gives
--
--   (1/2) Delta_k <= Delta_k + r_k.
--
-- The result constructs the existing HRBetaRemainderDominance carrier and then
-- reuses the all-scale induction.  The physical work is exactly the uniform
-- remainder estimate and one-step preservation of the selected admissible
-- interval.
------------------------------------------------------------------------

record OrderedAdditiveGroupMeaning
    {Scale Scalar : Set}
    {convention : Dyadic.DyadicRunningCouplingConvention Scale Scalar}
    (control : Dyadic.HRBetaRemainderControl convention) : Set₁ where
  field
    zero : Scalar
    negate : Scalar → Scalar

    transitive : ∀ {left middle right} →
      Dyadic.LessEqual control left middle →
      Dyadic.LessEqual control middle right →
      Dyadic.LessEqual control left right

    addMonotoneLeft : ∀ {lower upper} common →
      Dyadic.LessEqual control lower upper →
      Dyadic.LessEqual control
        (Dyadic.add control common lower)
        (Dyadic.add control common upper)

    addAssociative : ∀ left middle right →
      Dyadic.add control (Dyadic.add control left middle) right
      ≡ Dyadic.add control left (Dyadic.add control middle right)

    addZeroRight : ∀ value →
      Dyadic.add control value zero ≡ value

    addInverseRight : ∀ value →
      Dyadic.add control value (negate value) ≡ zero

    negateAntitone : ∀ {left right} →
      Dyadic.LessEqual control left right →
      Dyadic.LessEqual control (negate right) (negate left)

    negativeAbsoluteBelow : ∀ value →
      Dyadic.LessEqual control
        (negate (Dyadic.absolute control value)) value

    halfDecomposition : ∀ value →
      Dyadic.add control
        (Dyadic.halfOf control value)
        (Dyadic.halfOf control value)
      ≡ value

open OrderedAdditiveGroupMeaning public

leadingIncrement :
  ∀ {Scale Scalar}
    {convention : Dyadic.DyadicRunningCouplingConvention Scale Scalar} →
  Scale → Scalar
leadingIncrement {convention = convention} scale =
  P3.betaLogBlocking (Running.recursion (Dyadic.running convention)) scale

halfIncrementBelowNetIncrement :
  ∀ {Scale Scalar}
    {convention : Dyadic.DyadicRunningCouplingConvention Scale Scalar}
    {control : Dyadic.HRBetaRemainderControl convention}
    (algebra : OrderedAdditiveGroupMeaning control)
    scale →
  Dyadic.LessEqual control
    (Dyadic.halfOf control (leadingIncrement scale))
    (Dyadic.add control
      (leadingIncrement scale)
      (Dyadic.inverseCouplingRemainder control scale))
halfIncrementBelowNetIncrement {control = control} algebra scale =
  let
    increment = leadingIncrement scale
    halfIncrement = Dyadic.halfOf control increment
    remainder = Dyadic.inverseCouplingRemainder control scale
    negativeHalfBelowNegativeAbsolute =
      negateAntitone algebra
        (Dyadic.remainderBelowHalfDyadicIncrement control scale)
    negativeHalfBelowRemainder =
      transitive algebra
        negativeHalfBelowNegativeAbsolute
        (negativeAbsoluteBelow algebra remainder)
    zeroBelowHalfPlusRemainder =
      subst
        (λ lower → Dyadic.LessEqual control lower
          (Dyadic.add control halfIncrement remainder))
        (addInverseRight algebra halfIncrement)
        (addMonotoneLeft algebra halfIncrement
          negativeHalfBelowRemainder)
    halfBelowNestedSum =
      subst
        (λ lower → Dyadic.LessEqual control lower
          (Dyadic.add control halfIncrement
            (Dyadic.add control halfIncrement remainder)))
        (addZeroRight algebra halfIncrement)
        (addMonotoneLeft algebra halfIncrement
          zeroBelowHalfPlusRemainder)
    nestedSumEqualsNet =
      trans
        (sym (addAssociative algebra
          halfIncrement halfIncrement remainder))
        (cong
          (λ doubledHalf → Dyadic.add control doubledHalf remainder)
          (halfDecomposition algebra increment))
  in
  subst
    (λ upper → Dyadic.LessEqual control halfIncrement upper)
    nestedSumEqualsNet
    halfBelowNestedSum

record ScaleSuccessorMeaning
    {Scale Scalar : Set}
    {convention : Dyadic.DyadicRunningCouplingConvention Scale Scalar}
    (control : Dyadic.HRBetaRemainderControl convention) : Set₁ where
  field
    next : Scale → Scale
    previousNext : ∀ scale →
      Dyadic.previous control (next scale) ≡ scale

open ScaleSuccessorMeaning public

asHRBetaRemainderDominance :
  ∀ {Scale Scalar}
    {convention : Dyadic.DyadicRunningCouplingConvention Scale Scalar}
    {control : Dyadic.HRBetaRemainderControl convention}
    (algebra : OrderedAdditiveGroupMeaning control)
    (successor : ScaleSuccessorMeaning control) →
  Induction.HRBetaRemainderDominance Scale Scalar
asHRBetaRemainderDominance {control = control} algebra successor = record
  { Induction.HRBetaRemainderDominance.inverseCoupling =
      Dyadic.beta control
  ; Induction.HRBetaRemainderDominance.nextScale = next successor
  ; Induction.HRBetaRemainderDominance.leadingIncrement = λ scale →
      leadingIncrement (next successor scale)
  ; Induction.HRBetaRemainderDominance.remainder = λ scale →
      Dyadic.inverseCouplingRemainder control (next successor scale)
  ; Induction.HRBetaRemainderDominance.netIncrement = λ scale →
      Dyadic.add control
        (leadingIncrement (next successor scale))
        (Dyadic.inverseCouplingRemainder control (next successor scale))
  ; Induction.HRBetaRemainderDominance.betaLower = λ scale →
      Dyadic.halfOf control (leadingIncrement (next successor scale))
  ; Induction.HRBetaRemainderDominance.add = Dyadic.add control
  ; Induction.HRBetaRemainderDominance.LessEqual = Dyadic.LessEqual control
  ; Induction.HRBetaRemainderDominance.netIncrementMeaning = λ scale → refl
  ; Induction.HRBetaRemainderDominance.oneStepMeaning = λ scale →
      subst
        (λ previousScale →
          Dyadic.beta control (next successor scale)
          ≡ Dyadic.add control
              (Dyadic.beta control previousScale)
              (Dyadic.add control
                (leadingIncrement (next successor scale))
                (Dyadic.inverseCouplingRemainder control
                  (next successor scale))))
        (previousNext successor scale)
        (Dyadic.exactOneStepRecursion control (next successor scale))
  ; Induction.HRBetaRemainderDominance.betaDominatesRemainder = λ scale →
      halfIncrementBelowNetIncrement algebra (next successor scale)
  ; Induction.HRBetaRemainderDominance.addMonotoneLeft =
      addMonotoneLeft algebra
  }

record LowerIntervalAdmissibility
    {Scale Scalar : Set}
    {convention : Dyadic.DyadicRunningCouplingConvention Scale Scalar}
    {control : Dyadic.HRBetaRemainderControl convention}
    (algebra : OrderedAdditiveGroupMeaning control)
    (successor : ScaleSuccessorMeaning control) : Set₁ where
  field
    initialScale : Scale
    iterateScale : Nat → Scale
    iterateZero : iterateScale zero ≡ initialScale
    iterateSuccessor : ∀ count →
      iterateScale (suc count) ≡ next successor (iterateScale count)

    threshold : Scalar
    initialAboveThreshold :
      Dyadic.LessEqual control threshold
        (Dyadic.beta control initialScale)

    betaLowerNonnegative : ∀ scale →
      Dyadic.LessEqual control (zero algebra)
        (Induction.betaLower
          (asHRBetaRemainderDominance algebra successor) scale)

open LowerIntervalAdmissibility public

asPrimaryCouplingAdmissibilityInduction :
  ∀ {Scale Scalar}
    {convention : Dyadic.DyadicRunningCouplingConvention Scale Scalar}
    {control : Dyadic.HRBetaRemainderControl convention}
    {algebra : OrderedAdditiveGroupMeaning control}
    {successor : ScaleSuccessorMeaning control} →
  LowerIntervalAdmissibility algebra successor →
  Induction.PrimaryCouplingAdmissibilityInduction Scalar
asPrimaryCouplingAdmissibilityInduction {control = control}
    {algebra = algebra} {successor = successor} meaning = record
  { Induction.PrimaryCouplingAdmissibilityInduction.coupling = λ count →
      Dyadic.beta control (iterateScale meaning count)
  ; Induction.PrimaryCouplingAdmissibilityInduction.Admissible = λ value →
      Dyadic.LessEqual control (threshold meaning) value
  ; Induction.PrimaryCouplingAdmissibilityInduction.initialCouplingAdmissible =
      subst
        (λ selectedScale → Dyadic.LessEqual control
          (threshold meaning) (Dyadic.beta control selectedScale))
        (sym (iterateZero meaning))
        (initialAboveThreshold meaning)
  ; Induction.PrimaryCouplingAdmissibilityInduction.oneStepCouplingPreservesAdmissibility =
      λ count admissible →
        subst
          (λ selectedScale → Dyadic.LessEqual control
            (threshold meaning) (Dyadic.beta control selectedScale))
          (sym (iterateSuccessor meaning count))
          (transitive algebra
            admissible
            (transitive algebra
              (subst
                (λ lower → Dyadic.LessEqual control
                  lower
                  (Dyadic.add control
                    (Dyadic.beta control (iterateScale meaning count))
                    (Induction.betaLower
                      (asHRBetaRemainderDominance algebra successor)
                      (iterateScale meaning count))))
                (addZeroRight algebra
                  (Dyadic.beta control (iterateScale meaning count)))
                (addMonotoneLeft algebra
                  (Dyadic.beta control (iterateScale meaning count))
                  (betaLowerNonnegative meaning
                    (iterateScale meaning count))))
              (Induction.inverseCouplingGrowsByBetaLower
                (asHRBetaRemainderDominance algebra successor)
                (iterateScale meaning count))))
  }

allIteratedScalesAboveThreshold :
  ∀ {Scale Scalar}
    {convention : Dyadic.DyadicRunningCouplingConvention Scale Scalar}
    {control : Dyadic.HRBetaRemainderControl convention}
    {algebra : OrderedAdditiveGroupMeaning control}
    {successor : ScaleSuccessorMeaning control}
    (meaning : LowerIntervalAdmissibility algebra successor)
    count →
  Dyadic.LessEqual control (threshold meaning)
    (Dyadic.beta control (iterateScale meaning count))
allIteratedScalesAboveThreshold meaning count =
  Induction.allScalesCouplingAdmissible
    (asPrimaryCouplingAdmissibilityInduction meaning) count

halfRemainderDominanceLevel : ProofLevel
halfRemainderDominanceLevel = machineChecked

hrBetaDominanceCarrierAssemblyLevel : ProofLevel
hrBetaDominanceCarrierAssemblyLevel = machineChecked

lowerIntervalAllScaleAdmissibilityLevel : ProofLevel
lowerIntervalAllScaleAdmissibilityLevel = machineChecked

physicalHRBetaOrderedGroupInputsLevel : ProofLevel
physicalHRBetaOrderedGroupInputsLevel = conditional

physicalHRBetaSuccessorInputsLevel : ProofLevel
physicalHRBetaSuccessorInputsLevel = conditional

physicalHRBetaUniformRemainderInputsLevel : ProofLevel
physicalHRBetaUniformRemainderInputsLevel = conditional
