{-# OPTIONS --safe #-}
module DASHI.Physics.Closure.NSTriadKNR650ThreeSwapClosedClassWeightsRound770Exact where

------------------------------------------------------------------------
-- ROUND770 / R25/R130 THREE-CLASS QUOTIENT AS LEGAL R294
--            SWAP-INVARIANT FIXED-OUTPUT WEIGHTS
--
-- After R765 the independent triadic classes are:
--
--   LH U HL,   HH,   CC.
--
-- R130 proves exactly that p/q swap exchanges LH<->HL and preserves HH,CC.
-- Therefore their 0/1 indicator weights are legal R294
-- SwapInvariantCellWeight objects.
--
-- R294 then gives, separately for each of the three classes and each fixed
-- physical output fibre,
--
--   weighted product-rule fold = weighted commutator fold.
--
-- No magnitude, positivity, estimate, or heat/resolvent hypothesis is used.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadEnumeration as Physical
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadSymmetry as Symmetry
import DASHI.Physics.Closure.NSTriadKNPhysicalOutputFiber as Output
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNComLiteralBonyOutputFibrePartitionRound63Exact as Bony
import DASHI.Physics.Closure.NSTriadKNPhysicalBonyTagSwapRound130Exact as R130
import DASHI.Physics.Closure.NSTriadKNPeriodicHelicalFourierInfrastructure as Helical
import DASHI.Physics.Closure.NSTriadKNMixedHelicityFixedOutputSwapRound224Exact as R224
import DASHI.Physics.Closure.NSTriadKNResolventWeightedMixedCommutatorRound294Exact as R294

data SwapClosedClass : Set where
  lowHighUnion : SwapClosedClass
  highHigh : SwapClosedClass
  comparable : SwapClosedClass

classScalar :
  ∀ {r} (F : C3.RealField r) →
  SwapClosedClass →
  Bony.BonyTag →
  C3.Complex F
classScalar F lowHighUnion Bony.lhTag = C3.complexOne F
classScalar F lowHighUnion Bony.hlTag = C3.complexOne F
classScalar F lowHighUnion Bony.hhToLowTag = C3.complexZero F
classScalar F lowHighUnion Bony.comparableTag = C3.complexZero F
classScalar F highHigh Bony.lhTag = C3.complexZero F
classScalar F highHigh Bony.hlTag = C3.complexZero F
classScalar F highHigh Bony.hhToLowTag = C3.complexOne F
classScalar F highHigh Bony.comparableTag = C3.complexZero F
classScalar F comparable Bony.lhTag = C3.complexZero F
classScalar F comparable Bony.hlTag = C3.complexZero F
classScalar F comparable Bony.hhToLowTag = C3.complexZero F
classScalar F comparable Bony.comparableTag = C3.complexOne F

classCellWeight :
  ∀ {r} (F : C3.RealField r) →
  SwapClosedClass →
  Physical.PhysicalTriadIncidence →
  C3.Complex F
classCellWeight F selected tau =
  classScalar F selected (Bony.bonyTag tau)

classScalarSwapInvariant :
  ∀ {r} (F : C3.RealField r) →
  (selected : SwapClosedClass) →
  (tag : Bony.BonyTag) →
  classScalar F selected (R130.swapBonyTag tag)
  ≡ classScalar F selected tag
classScalarSwapInvariant F lowHighUnion Bony.lhTag = refl
classScalarSwapInvariant F lowHighUnion Bony.hlTag = refl
classScalarSwapInvariant F lowHighUnion Bony.hhToLowTag = refl
classScalarSwapInvariant F lowHighUnion Bony.comparableTag = refl
classScalarSwapInvariant F highHigh Bony.lhTag = refl
classScalarSwapInvariant F highHigh Bony.hlTag = refl
classScalarSwapInvariant F highHigh Bony.hhToLowTag = refl
classScalarSwapInvariant F highHigh Bony.comparableTag = refl
classScalarSwapInvariant F comparable Bony.lhTag = refl
classScalarSwapInvariant F comparable Bony.hlTag = refl
classScalarSwapInvariant F comparable Bony.hhToLowTag = refl
classScalarSwapInvariant F comparable Bony.comparableTag = refl

classCellWeightSwapInvariant :
  ∀ {r} (F : C3.RealField r) →
  (selected : SwapClosedClass) →
  (tau : Physical.PhysicalTriadIncidence) →
  classCellWeight F selected (Symmetry.swapTriad tau)
  ≡ classCellWeight F selected tau
classCellWeightSwapInvariant F selected tau =
  let
    tag = Bony.bonyTag tau
  in
  trans
    (cong
      (classScalar F selected)
      (R130.bonyTagSwapEquivariant tau))
    (classScalarSwapInvariant F selected tag)
classWeight :
  ∀ {r} (F : C3.RealField r) →
  SwapClosedClass →
  R294.SwapInvariantCellWeight F
classWeight F selected = record
  { R294.weight = classCellWeight F selected
  ; R294.swapInvariant = classCellWeightSwapInvariant F selected
  }

fixedOutputClassProductRuleIsCommutator :
  ∀ {r} {F : C3.RealField r}
    {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E} →
  (selected : SwapClosedClass) →
  (S : Helical.HelicalModeScalars F) →
  (velocity forcing : Z3.FourierMode → C3.Complex3 F) →
  (cutoff : Nat) →
  (output : Z3.FourierMode) →
  R224.foldVector
    (R294.weightedProductRuleCell
      (classWeight F selected) S velocity forcing)
    (Output.physicalOutputFiber
      cutoff output)
  ≡
  R224.foldVector
    (R294.weightedCommutatorCell
      (classWeight F selected) S velocity forcing)
    (Output.physicalOutputFiber
      cutoff output)
fixedOutputClassProductRuleIsCommutator
    selected S velocity forcing cutoff output =
  R294.fixedOutputWeightedProductRuleIsCommutator
    (classWeight _ selected)
    S velocity forcing cutoff output

------------------------------------------------------------------------
-- Status.
------------------------------------------------------------------------

round770ExactlyThreeSwapClosedR25Classes : Bool
round770ExactlyThreeSwapClosedR25Classes = true

round770LowHighUnionWeightSwapInvariant : Bool
round770LowHighUnionWeightSwapInvariant = true

round770HighHighWeightSwapInvariant : Bool
round770HighHighWeightSwapInvariant = true

round770ComparableWeightSwapInvariant : Bool
round770ComparableWeightSwapInvariant = true

round770ThreeClassFixedOutputProductRuleCollapseClosed : Bool
round770ThreeClassFixedOutputProductRuleCollapseClosed = true

round770IntroducesEstimate : Bool
round770IntroducesEstimate = false

round770ClayPromotion : Bool
round770ClayPromotion = false

round770ExactlyThreeSwapClosedR25ClassesIsTrue :
  round770ExactlyThreeSwapClosedR25Classes ≡ true
round770ExactlyThreeSwapClosedR25ClassesIsTrue = refl

round770LowHighUnionWeightSwapInvariantIsTrue :
  round770LowHighUnionWeightSwapInvariant ≡ true
round770LowHighUnionWeightSwapInvariantIsTrue = refl

round770HighHighWeightSwapInvariantIsTrue :
  round770HighHighWeightSwapInvariant ≡ true
round770HighHighWeightSwapInvariantIsTrue = refl

round770ComparableWeightSwapInvariantIsTrue :
  round770ComparableWeightSwapInvariant ≡ true
round770ComparableWeightSwapInvariantIsTrue = refl

round770ThreeClassFixedOutputProductRuleCollapseClosedIsTrue :
  round770ThreeClassFixedOutputProductRuleCollapseClosed ≡ true
round770ThreeClassFixedOutputProductRuleCollapseClosedIsTrue = refl

round770IntroducesEstimateIsFalse :
  round770IntroducesEstimate ≡ false
round770IntroducesEstimateIsFalse = refl

round770ClayPromotionIsFalse :
  round770ClayPromotion ≡ false
round770ClayPromotionIsFalse = refl
