module DASHI.Physics.YangMills.YMClayCMP102Section39TwoOuterWingsAcceptanceExact where

------------------------------------------------------------------------
-- Original scalar CMP102 Section39 native boundary.
-- Full signed last-B wing (for negative/zero/positive X) is
-- source-paid from original CMP109 factorial coefficients, standard
-- Bishop |pow| transport and the TRUE quarter-radius bound.
--
-- Original c=0 is independently paid; the ONLY retained
-- conditional inputs are A(c-1) and B(c-2) shifted outer
-- Cauchy wing order. These are NOT passed off as proven.
-- Actual physical Wilson F19/CMP116/OS/same-H mass gap separate.
-- Requires Agda 2.9 native --safe source/import elaboration.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat; suc)
import Real as R
import DASHI.Physics.YangMills.BalabanBishopConcreteHalfBallSquareExact as Half
import DASHI.Physics.YangMills.YMClayCMP102OriginalFiniteTailGeometryExact as Tail
import DASHI.Physics.YangMills.YMClayCMP102OriginalOmittedBPositiveWingExact as B
import DASHI.Physics.YangMills.YMClayCMP102OriginalTwoOuterWingsToLimitExact as Outer
import DASHI.Physics.YangMills.YMClayCMP102OriginalThreeWingOrderWeldExact as Three
import DASHI.Physics.YangMills.YMClayCMP102OriginalGFiniteLimitTransportExact as Original

originalNativeActualLastBAbsoluteFactor =
  B.originalOmittedBAbsoluteFactor

originalNativeActualLastBQuarterOrder :
  ∀ X (inside : R._≤_ (R.∣ X ∣) Half.bishopQuarter) n →
  R._≤_
    (R.∣ Tail.originalOmittedLinearB X n ∣)
    (R.pow Half.bishopQuarter (suc n))
originalNativeActualLastBQuarterOrder X inside n =
  B.originalOmittedBQuarterWing X inside n

originalNativeActualThreeFromTwo :
  ∀ X (inside : R._≤_ (R.∣ X ∣) Half.bishopQuarter) →
  Outer.OriginalOuterTwoWings X →
  Three.OriginalThreeWingOrder X
originalNativeActualThreeFromTwo =
  Outer.originalThreeWingsFromActualTwoOuter

originalNativeScalarZeroConditionalOnlyOnTwoOuter :
  ∀ X (inside : R._≤_ (R.∣ X ∣) Half.bishopQuarter) →
  Outer.OriginalOuterTwoWings X →
  R._≃_ (Original.originalG X inside) R.0ℝ
originalNativeScalarZeroConditionalOnlyOnTwoOuter =
  Outer.originalGZeroFromActualTwoOuterWings
