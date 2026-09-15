{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanSourceDecayRateSplitRound359Exact where

------------------------------------------------------------------------
-- ROUND359 / SOURCE RATE CALIBRATION = ONE POSITIVE SPLIT WITH SLACK
--
-- R357 asks for
--
--   deltaCollar <= deltaMark
--   residualKappa <= kappa
--   deltaCollar + residualKappa <= kappa.
--
-- CMP109/CMP116 use the standard source pattern of spending part of a positive
-- exponential localization exponent while retaining a still-positive residual
-- exponent.  Therefore the source-facing datum should be the split itself,
-- rather than three independently proved inequalities.
--
-- This owner proves the order consequences from a nonnegative split.  It does
-- NOT manufacture the physical values of the source exponents or identify them
-- with the selected CMP109/CMP116 carrier.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality using (subst)

open import DASHI.Foundations.RealAnalysisAxioms using
  ( ℝ ; 0ℝ ; _+ℝ_ ; _≤ℝ_
  ; ≤ℝ-refl ; ≤ℝ-trans ; +-mono-≤ ; +-identityˡ ; +-identityʳ )
open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanCoefficientCollarWeightRound357Exact as R357

record SourceDecayRateSplit : Set₁ where
  field
    deltaCollar deltaSlack residualKappa kappaSlack : ℝ

    deltaCollarNonnegative : 0ℝ ≤ℝ deltaCollar
    deltaSlackNonnegative : 0ℝ ≤ℝ deltaSlack
    residualKappaNonnegative : 0ℝ ≤ℝ residualKappa
    kappaSlackNonnegative : 0ℝ ≤ℝ kappaSlack

open SourceDecayRateSplit public

deltaMark : SourceDecayRateSplit → ℝ
deltaMark dataSet = deltaCollar dataSet +ℝ deltaSlack dataSet

kappa : SourceDecayRateSplit → ℝ
kappa dataSet =
  (deltaCollar dataSet +ℝ residualKappa dataSet) +ℝ kappaSlack dataSet

deltaMarkNonnegative :
  (dataSet : SourceDecayRateSplit) →
  0ℝ ≤ℝ deltaMark dataSet
deltaMarkNonnegative dataSet =
  subst
    (λ left → left ≤ℝ deltaMark dataSet)
    (+-identityˡ 0ℝ)
    (+-mono-≤
      (deltaCollarNonnegative dataSet)
      (deltaSlackNonnegative dataSet))

collarRateBelowMarkedRate :
  (dataSet : SourceDecayRateSplit) →
  deltaCollar dataSet ≤ℝ deltaMark dataSet
collarRateBelowMarkedRate dataSet =
  subst
    (λ left → left ≤ℝ deltaMark dataSet)
    (+-identityʳ (deltaCollar dataSet))
    (+-mono-≤ ≤ℝ-refl (deltaSlackNonnegative dataSet))

collarPlusResidualBelowKappa :
  (dataSet : SourceDecayRateSplit) →
  deltaCollar dataSet +ℝ residualKappa dataSet ≤ℝ kappa dataSet
collarPlusResidualBelowKappa dataSet =
  subst
    (λ left → left ≤ℝ kappa dataSet)
    (+-identityʳ (deltaCollar dataSet +ℝ residualKappa dataSet))
    (+-mono-≤ ≤ℝ-refl (kappaSlackNonnegative dataSet))

residualBelowCollarPlusResidual :
  (dataSet : SourceDecayRateSplit) →
  residualKappa dataSet
    ≤ℝ deltaCollar dataSet +ℝ residualKappa dataSet
residualBelowCollarPlusResidual dataSet =
  subst
    (λ left → left ≤ℝ deltaCollar dataSet +ℝ residualKappa dataSet)
    (+-identityˡ (residualKappa dataSet))
    (+-mono-≤ (deltaCollarNonnegative dataSet) ≤ℝ-refl)

residualRateBelowKappa :
  (dataSet : SourceDecayRateSplit) →
  residualKappa dataSet ≤ℝ kappa dataSet
residualRateBelowKappa dataSet =
  ≤ℝ-trans
    (residualBelowCollarPlusResidual dataSet)
    (collarPlusResidualBelowKappa dataSet)

record SourceRateApplication : Set₁ where
  field
    split : SourceDecayRateSplit
    collarRadius markedDistance treeLength : ℝ

    collarRadiusNonnegative : 0ℝ ≤ℝ collarRadius
    markedDistanceNonnegative : 0ℝ ≤ℝ markedDistance
    treeLengthNonnegative : 0ℝ ≤ℝ treeLength

open SourceRateApplication public

asR357Calibration :
  SourceRateApplication →
  R357.CoefficientCollarWeightCalibration
asR357Calibration dataSet = record
  { R357.CoefficientCollarWeightCalibration.deltaCollar =
      deltaCollar (split dataSet)
  ; R357.CoefficientCollarWeightCalibration.deltaMark =
      deltaMark (split dataSet)
  ; R357.CoefficientCollarWeightCalibration.residualKappa =
      residualKappa (split dataSet)
  ; R357.CoefficientCollarWeightCalibration.kappa =
      kappa (split dataSet)
  ; R357.CoefficientCollarWeightCalibration.collarRadius =
      collarRadius dataSet
  ; R357.CoefficientCollarWeightCalibration.markedDistance =
      markedDistance dataSet
  ; R357.CoefficientCollarWeightCalibration.treeLength =
      treeLength dataSet
  ; R357.CoefficientCollarWeightCalibration.deltaCollarNonnegative =
      deltaCollarNonnegative (split dataSet)
  ; R357.CoefficientCollarWeightCalibration.deltaMarkNonnegative =
      deltaMarkNonnegative (split dataSet)
  ; R357.CoefficientCollarWeightCalibration.residualKappaNonnegative =
      residualKappaNonnegative (split dataSet)
  ; R357.CoefficientCollarWeightCalibration.collarRadiusNonnegative =
      collarRadiusNonnegative dataSet
  ; R357.CoefficientCollarWeightCalibration.markedDistanceNonnegative =
      markedDistanceNonnegative dataSet
  ; R357.CoefficientCollarWeightCalibration.treeLengthNonnegative =
      treeLengthNonnegative dataSet
  ; R357.CoefficientCollarWeightCalibration.markedRateDominatesCollarRate =
      collarRateBelowMarkedRate (split dataSet)
  ; R357.CoefficientCollarWeightCalibration.residualRateBelowKappa =
      residualRateBelowKappa (split dataSet)
  ; R357.CoefficientCollarWeightCalibration.totalCollarResidualRateBelowKappa =
      collarPlusResidualBelowKappa (split dataSet)
  }

------------------------------------------------------------------------
-- Pareto/source accounting.
------------------------------------------------------------------------

rateSplitOrderCompilerLevel : ProofLevel
rateSplitOrderCompilerLevel = machineChecked

literalCMP109CMP116PositiveRateSplitAttachmentLevel : ProofLevel
literalCMP109CMP116PositiveRateSplitAttachmentLevel = conditional

threeIndependentRateInequalitiesArePrimitive : Bool
threeIndependentRateInequalitiesArePrimitive = false

threeIndependentRateInequalitiesArePrimitiveIsFalse :
  threeIndependentRateInequalitiesArePrimitive ≡ false
threeIndependentRateInequalitiesArePrimitiveIsFalse = refl

sourceRateSplitStillRequiresSameCarrierAttachment : Bool
sourceRateSplitStillRequiresSameCarrierAttachment = true

sourceRateSplitStillRequiresSameCarrierAttachmentIsTrue :
  sourceRateSplitStillRequiresSameCarrierAttachment ≡ true
sourceRateSplitStillRequiresSameCarrierAttachmentIsTrue = refl

record Round359Boundary : Set where
  constructor round359-boundary
  field
    orderCalibrationCompilerOwned : Bool
    orderCalibrationCompilerOwnedIsTrue :
      orderCalibrationCompilerOwned ≡ true

    onePositiveSourceRateSplitStillOpen : Bool
    onePositiveSourceRateSplitStillOpenIsTrue :
      onePositiveSourceRateSplitStillOpen ≡ true

canonicalRound359Boundary : Round359Boundary
canonicalRound359Boundary =
  round359-boundary true refl true refl

round359FrontierRefinementLevel : ProofLevel
round359FrontierRefinementLevel = machineChecked

clayPromotion : Bool
clayPromotion = false

clayPromotionIsFalse : clayPromotion ≡ false
clayPromotionIsFalse = refl
