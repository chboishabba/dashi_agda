{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanSelectedDistanceCarrierWeldRound349Exact where

------------------------------------------------------------------------
-- ROUND349 / REUSE R304 DISTANCE=TIME ON THE EXACT R300 SELECTED PAIR
--
-- R346 leaves
--
--   D_time : R318.physicalDistance(selected left,right) = time.
--
-- R304 already owns the SAME selected-pair theorem, using the SAME R300
-- `indexFor decomposition observable time`, but its distance is read from the
-- older R284 `directShell` carrier.  Re-proving Euclidean-time semantics is
-- therefore overpayment.
--
-- The only residual payment is the selected-pair carrier weld
--
--   R318.physicalDistance(left_t,right_t)
--     = R284.physicalDistance(directShell,left_t,right_t).
--
-- R304's existing theorem then gives R346 D_time by transitivity.  No change of
-- spectral pair, observable, time, or decomposition is permitted by this ABI.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational.Base using (ℚ)
open import Relation.Binary.PropositionalEquality using (trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanClayT5PhysicalMeasureGramContinuityExact as Gram
import DASHI.Physics.YangMills.BalabanConnectedCovarianceExpectationLimitRound278Exact as R278
import DASHI.Physics.YangMills.BalabanT5UnlocalizedJSourceLocalizationRound318Exact as R318
import DASHI.Physics.YangMills.BalabanCMP116DirectT5ContinuumClusteringRound284Exact as R284
import DASHI.Physics.YangMills.BalabanQuantitativePositiveTimeCyclicityRound299Exact as R299
import DASHI.Physics.YangMills.BalabanCyclicSubgapNonzeroByConstructionRound297Exact as R297
import DASHI.Physics.YangMills.BalabanPositiveSpectralComponentLowerRound300Exact as R300
import DASHI.Physics.YangMills.BalabanModeSelectedDirectT5ContinuumUpperRound304Exact as R304

record SelectedDistanceCarrierWeld
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
    r318DistanceIsR284Distance : ∀ observable time →
      let index = R300.indexFor decomposition observable time in
      R318.physicalDistance base
        (R278.left tests index) (R278.right tests index)
      ≡
      R284.physicalDistance (R304.directShell payment)
        (R278.left tests index) (R278.right tests index)

open SelectedDistanceCarrierWeld public

selectedR318DistanceIsTime :
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
  SelectedDistanceCarrierWeld base tests quantitative family decomposition payment →
  ∀ observable time →
  let index = R300.indexFor decomposition observable time in
  R318.physicalDistance base
    (R278.left tests index) (R278.right tests index)
  ≡ time
selectedR318DistanceIsTime {payment = payment} weld observable time =
  trans
    (r318DistanceIsR284Distance weld observable time)
    (R304.selectedPairDistanceIsTime payment observable time)

------------------------------------------------------------------------
-- Pareto/status boundary.
------------------------------------------------------------------------

r304SelectedDistanceTimeDonorOwned : Bool
r304SelectedDistanceTimeDonorOwned = true

r304SelectedDistanceTimeDonorOwnedIsTrue :
  r304SelectedDistanceTimeDonorOwned ≡ true
r304SelectedDistanceTimeDonorOwnedIsTrue = refl

-- Only the carrier equality above remains physical/same-object debt.
selectedDistanceCarrierWeldLevel : ProofLevel
selectedDistanceCarrierWeldLevel = conditional

selectedDistanceTimeCompilerLevel : ProofLevel
selectedDistanceTimeCompilerLevel = machineChecked

freshSelectedDistanceTimeAnalysisRequired : Bool
freshSelectedDistanceTimeAnalysisRequired = false

freshSelectedDistanceTimeAnalysisRequiredIsFalse :
  freshSelectedDistanceTimeAnalysisRequired ≡ false
freshSelectedDistanceTimeAnalysisRequiredIsFalse = refl

selectedPairChangedByTransport : Bool
selectedPairChangedByTransport = false

selectedPairChangedByTransportIsFalse :
  selectedPairChangedByTransport ≡ false
selectedPairChangedByTransportIsFalse = refl

record Round349Boundary : Set where
  constructor round349-boundary
  field
    r304DistanceTimeReused : Bool
    r304DistanceTimeReusedIsTrue : r304DistanceTimeReused ≡ true

    selectedDistanceCarrierWeldStillPhysical : Bool
    selectedDistanceCarrierWeldStillPhysicalIsTrue :
      selectedDistanceCarrierWeldStillPhysical ≡ true

    freshTimeSemanticsPruned : Bool
    freshTimeSemanticsPrunedIsTrue : freshTimeSemanticsPruned ≡ true

canonicalRound349Boundary : Round349Boundary
canonicalRound349Boundary =
  round349-boundary true refl true refl true refl

round349FrontierRefinementLevel : ProofLevel
round349FrontierRefinementLevel = machineChecked

clayPromotion : Bool
clayPromotion = false

clayPromotionIsFalse : clayPromotion ≡ false
clayPromotionIsFalse = refl
