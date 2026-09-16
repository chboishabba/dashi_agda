{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanSelectedDistanceCarrierLowerRound392Exact where

------------------------------------------------------------------------
-- ROUND392 / R349 CARRIER EQUALITY -> ONE-SIDED SELECTED COMPARISON
--
-- R304 already proves, on the exact R300 selected observable/time pair,
--
--   d_R284(selected pair) = time.
--
-- R349 asks for the stronger cross-carrier identity
--
--   d_R318(selected pair) = d_R284(selected pair)
--
-- in order to recover d_R318 = time.  R390/R391 show the decreasing clustering
-- envelope only needs time <= d_R318.  Hence the least-privilege carrier weld is
--
--   d_R284(selected pair) <= d_R318(selected pair).
--
-- R304's exact theorem then compiles this to the R391 geometry input.  No pair,
-- observable, time, or spectral decomposition may change across the weld.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
import Data.Nat.Base as Nat
open import Data.Rational.Base using (ℚ)
open import Relation.Binary.PropositionalEquality using (subst)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanClayT5PhysicalMeasureGramContinuityExact as Gram
import DASHI.Physics.YangMills.BalabanConnectedCovarianceExpectationLimitRound278Exact as R278
import DASHI.Physics.YangMills.BalabanT5UnlocalizedJSourceLocalizationRound318Exact as R318
import DASHI.Physics.YangMills.BalabanCMP116DirectT5ContinuumClusteringRound284Exact as R284
import DASHI.Physics.YangMills.BalabanQuantitativePositiveTimeCyclicityRound299Exact as R299
import DASHI.Physics.YangMills.BalabanCyclicSubgapNonzeroByConstructionRound297Exact as R297
import DASHI.Physics.YangMills.BalabanPositiveSpectralComponentLowerRound300Exact as R300
import DASHI.Physics.YangMills.BalabanModeSelectedDirectT5ContinuumUpperRound304Exact as R304

record SelectedDistanceCarrierLowerWeld
    {Measure TestObservable Energy Vector : Set}
    {dataSet : Gram.PhysicalMeasureConvergenceData Measure TestObservable ℚ}
    {extension : R278.ScalarCovarianceConvergenceExtension dataSet}
    (base : R318.UnlocalizedT5StateFamilyJPresentation dataSet extension)
    (tests : R278.SelectedConnectedCovarianceTests dataSet)
    (quantitative : R299.QuantitativePositiveTimeVacuumCyclicity TestObservable Vector)
    (family : R297.ActualNonzeroSubgapFamily
      (R299.asPositiveTimeVacuumCyclicity quantitative))
    (decomposition : R300.PositiveSpectralComponentDecomposition
      dataSet extension tests quantitative family)
    (payment : R304.ModeSelectedDirectT5UpperPayment
      dataSet extension tests quantitative family decomposition)
    : Set₁ where
  field
    r284DistanceBelowR318Distance : ∀ observable time →
      let index = R300.indexFor decomposition observable time in
      R284.physicalDistance (R304.directShell payment)
        (R278.left tests index) (R278.right tests index)
      Nat.≤
      R318.physicalDistance base
        (R278.left tests index) (R278.right tests index)

open SelectedDistanceCarrierLowerWeld public

selectedTimeBelowR318Distance :
  ∀ {Measure TestObservable Energy Vector}
    {dataSet : Gram.PhysicalMeasureConvergenceData Measure TestObservable ℚ}
    {extension : R278.ScalarCovarianceConvergenceExtension dataSet}
    {base : R318.UnlocalizedT5StateFamilyJPresentation dataSet extension}
    {tests : R278.SelectedConnectedCovarianceTests dataSet}
    {quantitative : R299.QuantitativePositiveTimeVacuumCyclicity TestObservable Vector}
    {family : R297.ActualNonzeroSubgapFamily
      (R299.asPositiveTimeVacuumCyclicity quantitative)}
    {decomposition : R300.PositiveSpectralComponentDecomposition
      dataSet extension tests quantitative family}
    {payment : R304.ModeSelectedDirectT5UpperPayment
      dataSet extension tests quantitative family decomposition} →
  SelectedDistanceCarrierLowerWeld
    base tests quantitative family decomposition payment →
  ∀ observable time →
  let index = R300.indexFor decomposition observable time in
  time Nat.≤ R318.physicalDistance base
    (R278.left tests index) (R278.right tests index)
selectedTimeBelowR318Distance {payment = payment} weld observable time =
  subst
    (λ oldDistance →
      oldDistance Nat.≤
      R318.physicalDistance _
        (R278.left _ (R300.indexFor _ observable time))
        (R278.right _ (R300.indexFor _ observable time)))
    (R304.selectedPairDistanceIsTime payment observable time)
    (r284DistanceBelowR318Distance weld observable time)

------------------------------------------------------------------------
-- Pareto / authority boundary.
------------------------------------------------------------------------

round392SelectedDistanceLowerCompilerLevel : ProofLevel
round392SelectedDistanceLowerCompilerLevel = machineChecked

r349ExactCarrierEqualityMandatory : Bool
r349ExactCarrierEqualityMandatory = false

r349ExactCarrierEqualityMandatoryIsFalse :
  r349ExactCarrierEqualityMandatory ≡ false
r349ExactCarrierEqualityMandatoryIsFalse = refl

selectedCarrierLowerComparisonStillProofBearing : Bool
selectedCarrierLowerComparisonStillProofBearing = true

selectedCarrierLowerComparisonStillProofBearingIsTrue :
  selectedCarrierLowerComparisonStillProofBearing ≡ true
selectedCarrierLowerComparisonStillProofBearingIsTrue = refl

selectedPairAndTimePreserved : Bool
selectedPairAndTimePreserved = true

selectedPairAndTimePreservedIsTrue :
  selectedPairAndTimePreserved ≡ true
selectedPairAndTimePreservedIsTrue = refl

record Round392Boundary : Set where
  constructor round392-boundary
  field
    r304DistanceTimeTheoremReused : Bool
    r304DistanceTimeTheoremReusedIsTrue :
      r304DistanceTimeTheoremReused ≡ true

    exactCrossCarrierEqualityPruned : Bool
    exactCrossCarrierEqualityPrunedIsTrue :
      exactCrossCarrierEqualityPruned ≡ true

    oneSidedCarrierGeometryStillPhysical : Bool
    oneSidedCarrierGeometryStillPhysicalIsTrue :
      oneSidedCarrierGeometryStillPhysical ≡ true

canonicalRound392Boundary : Round392Boundary
canonicalRound392Boundary = round392-boundary true refl true refl true refl

clayPromotion : Bool
clayPromotion = false

clayPromotionIsFalse : clayPromotion ≡ false
