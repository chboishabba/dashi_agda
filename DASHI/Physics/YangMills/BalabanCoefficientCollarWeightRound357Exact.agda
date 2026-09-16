{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanCoefficientCollarWeightRound357Exact where

------------------------------------------------------------------------
-- ROUND357 / WEIGHT CALIBRATION IS NOT A NEW GEOMETRIC THEOREM
--
-- R356 removes the connected-span part of the large-X branch.  R355 still
-- states both branches after multiplication by decay rates.  The weighted
-- inequalities follow from ordinary ordered-ring monotonicity once source
-- acquisition supplies:
--
--   * the unweighted collar alternative R <= d_mark OR R <= treeLength;
--   * nonnegative source distances/rates;
--   * delta_collar <= delta_mark;
--   * delta_collar + kappa' <= kappa;
--   * kappa' <= kappa.
--
-- This file proves that compiler and constructs the exact R355 charge object.
-- It does not supply the source metric attachments or choose the physical decay
-- constants.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (subst; sym)

open import DASHI.Foundations.RealAnalysisAxioms using
  ( ℝ ; 0ℝ ; _+ℝ_ ; _*ℝ_ ; _≤ℝ_
  ; ≤ℝ-refl ; ≤ℝ-trans ; +-mono-≤ ; +-identityˡ
  ; *-distribʳ-+ ; mulMonotoneNonnegative ; mulZeroʳ )
open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Physics.YangMills.BalabanCoefficientCollarChargeRound355Exact as R355

record CoefficientCollarWeightCalibration : Set₁ where
  field
    deltaCollar deltaMark residualKappa kappa : ℝ
    collarRadius markedDistance treeLength : ℝ

    deltaCollarNonnegative : 0ℝ ≤ℝ deltaCollar
    deltaMarkNonnegative : 0ℝ ≤ℝ deltaMark
    residualKappaNonnegative : 0ℝ ≤ℝ residualKappa
    collarRadiusNonnegative : 0ℝ ≤ℝ collarRadius
    markedDistanceNonnegative : 0ℝ ≤ℝ markedDistance
    treeLengthNonnegative : 0ℝ ≤ℝ treeLength

    markedRateDominatesCollarRate : deltaCollar ≤ℝ deltaMark
    residualRateBelowKappa : residualKappa ≤ℝ kappa
    totalCollarResidualRateBelowKappa :
      deltaCollar +ℝ residualKappa ≤ℝ kappa

open CoefficientCollarWeightCalibration public

productNonnegative :
  ∀ a b →
  0ℝ ≤ℝ a →
  0ℝ ≤ℝ b →
  0ℝ ≤ℝ a *ℝ b
productNonnegative a b a≥0 b≥0 =
  subst
    (λ lower → lower ≤ℝ a *ℝ b)
    (mulZeroʳ 0ℝ)
    (mulMonotoneNonnegative ≤ℝ-refl a≥0 ≤ℝ-refl b≥0)

sumRatesNonnegative :
  (dataSet : CoefficientCollarWeightCalibration) →
  0ℝ ≤ℝ deltaCollar dataSet +ℝ residualKappa dataSet
sumRatesNonnegative dataSet =
  subst
    (λ lower → lower ≤ℝ deltaCollar dataSet +ℝ residualKappa dataSet)
    (+-identityˡ 0ℝ)
    (+-mono-≤
      (deltaCollarNonnegative dataSet)
      (residualKappaNonnegative dataSet))

markedDistancePaysWeightedCollar :
  (dataSet : CoefficientCollarWeightCalibration) →
  collarRadius dataSet ≤ℝ markedDistance dataSet →
  deltaCollar dataSet *ℝ collarRadius dataSet
    ≤ℝ deltaMark dataSet *ℝ markedDistance dataSet
markedDistancePaysWeightedCollar dataSet radius≤marked =
  mulMonotoneNonnegative
    (deltaCollarNonnegative dataSet)
    (markedRateDominatesCollarRate dataSet)
    (collarRadiusNonnegative dataSet)
    radius≤marked

collarWeightedBelowSameTree :
  (dataSet : CoefficientCollarWeightCalibration) →
  collarRadius dataSet ≤ℝ treeLength dataSet →
  deltaCollar dataSet *ℝ collarRadius dataSet
    ≤ℝ deltaCollar dataSet *ℝ treeLength dataSet
collarWeightedBelowSameTree dataSet radius≤tree =
  mulMonotoneNonnegative
    (deltaCollarNonnegative dataSet)
    ≤ℝ-refl
    (collarRadiusNonnegative dataSet)
    radius≤tree

sumWeightedByTree :
  (dataSet : CoefficientCollarWeightCalibration) →
  deltaCollar dataSet *ℝ treeLength dataSet
    +ℝ residualKappa dataSet *ℝ treeLength dataSet
    ≤ℝ kappa dataSet *ℝ treeLength dataSet
sumWeightedByTree dataSet =
  ≤ℝ-trans
    (subst
      (λ left → left ≤ℝ
        kappa dataSet *ℝ treeLength dataSet)
      (*-distribʳ-+
        (deltaCollar dataSet)
        (residualKappa dataSet)
        (treeLength dataSet))
      (mulMonotoneNonnegative
        (sumRatesNonnegative dataSet)
        (totalCollarResidualRateBelowKappa dataSet)
        (treeLengthNonnegative dataSet)
        ≤ℝ-refl))
    ≤ℝ-refl

largeTreePaysWeightedCollar :
  (dataSet : CoefficientCollarWeightCalibration) →
  collarRadius dataSet ≤ℝ treeLength dataSet →
  deltaCollar dataSet *ℝ collarRadius dataSet
    +ℝ residualKappa dataSet *ℝ treeLength dataSet
    ≤ℝ kappa dataSet *ℝ treeLength dataSet
largeTreePaysWeightedCollar dataSet radius≤tree =
  ≤ℝ-trans
    (+-mono-≤
      (collarWeightedBelowSameTree dataSet radius≤tree)
      ≤ℝ-refl)
    (sumWeightedByTree dataSet)

residualTreeBelowOriginalTree :
  (dataSet : CoefficientCollarWeightCalibration) →
  residualKappa dataSet *ℝ treeLength dataSet
    ≤ℝ kappa dataSet *ℝ treeLength dataSet
residualTreeBelowOriginalTree dataSet =
  mulMonotoneNonnegative
    (residualKappaNonnegative dataSet)
    (residualRateBelowKappa dataSet)
    (treeLengthNonnegative dataSet)
    ≤ℝ-refl

asR355ChargeGeometry :
  (dataSet : CoefficientCollarWeightCalibration) →
  (collarRadius dataSet ≤ℝ markedDistance dataSet)
    ⊎ (collarRadius dataSet ≤ℝ treeLength dataSet) →
  R355.CoefficientCollarChargeGeometry
asR355ChargeGeometry dataSet geometry = record
  { R355.CoefficientCollarChargeGeometry.deltaMark = deltaMark dataSet
  ; R355.CoefficientCollarChargeGeometry.markedDistance = markedDistance dataSet
  ; R355.CoefficientCollarChargeGeometry.kappa = kappa dataSet
  ; R355.CoefficientCollarChargeGeometry.treeLength = treeLength dataSet
  ; R355.CoefficientCollarChargeGeometry.deltaCollar = deltaCollar dataSet
  ; R355.CoefficientCollarChargeGeometry.collarRadius = collarRadius dataSet
  ; R355.CoefficientCollarChargeGeometry.residualKappa = residualKappa dataSet
  ; R355.CoefficientCollarChargeGeometry.markedChargeNonnegative =
      productNonnegative
        (deltaMark dataSet)
        (markedDistance dataSet)
        (deltaMarkNonnegative dataSet)
        (markedDistanceNonnegative dataSet)
  ; R355.CoefficientCollarChargeGeometry.residualTreeBelowOriginalTree =
      residualTreeBelowOriginalTree dataSet
  ; R355.CoefficientCollarChargeGeometry.coefficientCollarDichotomy =
      weightedDichotomy geometry
  }
  where
  weightedDichotomy :
    (collarRadius dataSet ≤ℝ markedDistance dataSet)
      ⊎ (collarRadius dataSet ≤ℝ treeLength dataSet) →
    (deltaCollar dataSet *ℝ collarRadius dataSet
      ≤ℝ deltaMark dataSet *ℝ markedDistance dataSet)
    ⊎
    ((deltaCollar dataSet *ℝ collarRadius dataSet)
      +ℝ (residualKappa dataSet *ℝ treeLength dataSet)
      ≤ℝ kappa dataSet *ℝ treeLength dataSet)
  weightedDichotomy (inj₁ marked) =
    inj₁ (markedDistancePaysWeightedCollar dataSet marked)
  weightedDichotomy (inj₂ large) =
    inj₂ (largeTreePaysWeightedCollar dataSet large)

------------------------------------------------------------------------
-- Pareto/source accounting.
------------------------------------------------------------------------

coefficientWeightCompilerLevel : ProofLevel
coefficientWeightCompilerLevel = machineChecked

-- Source/application acquisition is now explicit rather than hidden inside the
-- weighted majorant theorem.
literalCollarToMarkedDistanceAttachmentLevel : ProofLevel
literalCollarToMarkedDistanceAttachmentLevel = conditional

literalCollarToTreeLengthAttachmentLevel : ProofLevel
literalCollarToTreeLengthAttachmentLevel = conditional

literalDecayRateCalibrationLevel : ProofLevel
literalDecayRateCalibrationLevel = conditional

weightedR355BranchRequiresFreshAnalyticTheorem : Bool
weightedR355BranchRequiresFreshAnalyticTheorem = false

weightedR355BranchRequiresFreshAnalyticTheoremIsFalse :
  weightedR355BranchRequiresFreshAnalyticTheorem ≡ false
weightedR355BranchRequiresFreshAnalyticTheoremIsFalse = refl

record Round357Boundary : Set where
  constructor round357-boundary
  field
    weightedBranchCompilerOwned : Bool
    weightedBranchCompilerOwnedIsTrue : weightedBranchCompilerOwned ≡ true

    sourceMetricAttachmentsStillOpen : Bool
    sourceMetricAttachmentsStillOpenIsTrue : sourceMetricAttachmentsStillOpen ≡ true

    decayRateCalibrationStillOpen : Bool
    decayRateCalibrationStillOpenIsTrue : decayRateCalibrationStillOpen ≡ true

canonicalRound357Boundary : Round357Boundary
canonicalRound357Boundary =
  round357-boundary
    true refl
    true refl
    true refl

round357FrontierRefinementLevel : ProofLevel
round357FrontierRefinementLevel = machineChecked

clayPromotion : Bool
clayPromotion = false

clayPromotionIsFalse : clayPromotion ≡ false
