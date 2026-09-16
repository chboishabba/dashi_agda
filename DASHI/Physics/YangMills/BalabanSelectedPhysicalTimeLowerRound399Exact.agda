{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanSelectedPhysicalTimeLowerRound399Exact where

------------------------------------------------------------------------
-- ROUND399 / LEAST-PRIVILEGE SELECTED SUPPORT-TIME GEOMETRY
--
-- The historical physical pair presentation asks for exact
--
--     distance(selected left, time-translated right) = time.
--
-- The source-native decay consumer is monotone in distance and needs only
--
--     time <= distance(selected left, time-translated right).
--
-- R398 has already removed the independent R284/R318 distance carrier on the
-- preferred construction.  This owner therefore keeps only the one physical
-- geometry statement on the canonical R318 distance.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Nat.Base as Nat
open import Data.Rational.Base using (ℚ)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanClayT5PhysicalMeasureGramContinuityExact as Gram
import DASHI.Physics.YangMills.BalabanConnectedCovarianceExpectationLimitRound278Exact as R278
import DASHI.Physics.YangMills.BalabanT5UnlocalizedJSourceLocalizationRound318Exact as R318
import DASHI.Physics.YangMills.BalabanQuantitativePositiveTimeCyclicityRound299Exact as R299
import DASHI.Physics.YangMills.BalabanCyclicSubgapNonzeroByConstructionRound297Exact as R297
import DASHI.Physics.YangMills.BalabanPositiveSpectralComponentLowerRound300Exact as R300
import DASHI.Physics.YangMills.BalabanModeSelectedDirectT5ContinuumUpperRound304Exact as R304
import DASHI.Physics.YangMills.BalabanSelectedDistanceCarrierLowerRound392Exact as R392

record SelectedPhysicalTimeLower
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
    : Set₁ where
  field
    selectedTimeBelowPhysicalDistance : ∀ observable time →
      let index = R300.indexFor decomposition observable time in
      time Nat.≤ R318.physicalDistance base
        (R278.left tests index) (R278.right tests index)

open SelectedPhysicalTimeLower public

fromR392 :
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
  R392.SelectedDistanceCarrierLowerWeld
    base tests quantitative family decomposition payment →
  SelectedPhysicalTimeLower base tests quantitative family decomposition
fromR392 weld = record
  { selectedTimeBelowPhysicalDistance =
      R392.selectedTimeBelowR318Distance weld
  }

------------------------------------------------------------------------
-- Pareto / authority boundary.
------------------------------------------------------------------------

round399GeometryCompilerLevel : ProofLevel
round399GeometryCompilerLevel = machineChecked

exactDistanceEqualsTimeRequired : Bool
exactDistanceEqualsTimeRequired = false

exactDistanceEqualsTimeRequiredIsFalse :
  exactDistanceEqualsTimeRequired ≡ false
exactDistanceEqualsTimeRequiredIsFalse = refl

independentDistanceCarrierWeldRequired : Bool
independentDistanceCarrierWeldRequired = false

independentDistanceCarrierWeldRequiredIsFalse :
  independentDistanceCarrierWeldRequired ≡ false
independentDistanceCarrierWeldRequiredIsFalse = refl

oneSidedSelectedSupportTimeGeometryStillProofBearing : Bool
oneSidedSelectedSupportTimeGeometryStillProofBearing = true

oneSidedSelectedSupportTimeGeometryStillProofBearingIsTrue :
  oneSidedSelectedSupportTimeGeometryStillProofBearing ≡ true
oneSidedSelectedSupportTimeGeometryStillProofBearingIsTrue = refl

clayPromotion : Bool
clayPromotion = false

clayPromotionIsFalse : clayPromotion ≡ false
clayPromotionIsFalse = refl
