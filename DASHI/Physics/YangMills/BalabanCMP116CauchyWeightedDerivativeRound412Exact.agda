{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanCMP116CauchyWeightedDerivativeRound412Exact where

------------------------------------------------------------------------
-- ROUND412 / CAUCHY DIFFERENTIATION PRESERVES AN EXTERNAL SPATIAL WEIGHT
--
-- CMP116's several-complex-variable step should not be represented merely by a
-- ProofLevel.  Algebraically, once
--
--   |D_JL D_JR H| <= C_Cauchy |H|
--   |H|            <= A W(distance)
--
-- with nonnegative factors, the SAME external spatial weight survives:
--
--   |D_JL D_JR H| <= (C_Cauchy A) W(distance).
--
-- The theorem below is real-valued and uses only the repository's standard
-- ordered-real multiplication laws.  It introduces no Yang--Mills estimate.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality using (subst; sym)

open import DASHI.Foundations.RealAnalysisAxioms using
  ( ℝ ; 0ℝ ; _*ℝ_ ; _≤ℝ_
  ; ≤ℝ-refl ; ≤ℝ-trans ; mulMonotoneNonnegative ; *-assoc )
open import DASHI.Physics.YangMills.CompactLieProofLevel

record CauchyWeightedDerivativeData
    (Domain Term : Set) : Set₁ where
  field
    baseActivityMagnitude : Domain → Term → ℝ
    differentiatedMagnitude : Domain → Term → ℝ

    cauchyDerivativeCost : ℝ
    sourceAmplitude : ℝ
    spatialWeight : Domain → Term → ℝ

    cauchyDerivativeCostNonnegative :
      0ℝ ≤ℝ cauchyDerivativeCost

    sourceAmplitudeNonnegative :
      0ℝ ≤ℝ sourceAmplitude

    spatialWeightNonnegative :
      ∀ domain term → 0ℝ ≤ℝ spatialWeight domain term

    baseActivityMagnitudeNonnegative :
      ∀ domain term → 0ℝ ≤ℝ baseActivityMagnitude domain term

    differentiatedMagnitudeBelowCauchyScale :
      ∀ domain term →
      differentiatedMagnitude domain term
      ≤ℝ cauchyDerivativeCost *ℝ baseActivityMagnitude domain term

    baseActivityBelowExternalSpatialEnvelope :
      ∀ domain term →
      baseActivityMagnitude domain term
      ≤ℝ sourceAmplitude *ℝ spatialWeight domain term

open CauchyWeightedDerivativeData public

cauchyDifferentiationPreservesExternalSpatialWeight :
  ∀ {Domain Term}
    (dataSet : CauchyWeightedDerivativeData Domain Term)
    domain term →
  differentiatedMagnitude dataSet domain term
  ≤ℝ
  (cauchyDerivativeCost dataSet *ℝ sourceAmplitude dataSet)
    *ℝ spatialWeight dataSet domain term
cauchyDifferentiationPreservesExternalSpatialWeight dataSet domain term =
  let
    weightNN = spatialWeightNonnegative dataSet domain term

    amplitudeWeightNN :
      0ℝ ≤ℝ sourceAmplitude dataSet *ℝ spatialWeight dataSet domain term
    amplitudeWeightNN =
      mulMonotoneNonnegative
        (sourceAmplitudeNonnegative dataSet)
        ≤ℝ-refl
        weightNN
        ≤ℝ-refl

    scaledBase :
      cauchyDerivativeCost dataSet *ℝ baseActivityMagnitude dataSet domain term
      ≤ℝ
      cauchyDerivativeCost dataSet *ℝ
        (sourceAmplitude dataSet *ℝ spatialWeight dataSet domain term)
    scaledBase =
      mulMonotoneNonnegative
        (cauchyDerivativeCostNonnegative dataSet)
        ≤ℝ-refl
        (baseActivityMagnitudeNonnegative dataSet domain term)
        (baseActivityBelowExternalSpatialEnvelope dataSet domain term)

    composed :
      differentiatedMagnitude dataSet domain term
      ≤ℝ
      cauchyDerivativeCost dataSet *ℝ
        (sourceAmplitude dataSet *ℝ spatialWeight dataSet domain term)
    composed =
      ≤ℝ-trans
        (differentiatedMagnitudeBelowCauchyScale dataSet domain term)
        scaledBase
  in
  subst
    (λ upper →
      differentiatedMagnitude dataSet domain term ≤ℝ upper)
    (sym (*-assoc
      (cauchyDerivativeCost dataSet)
      (sourceAmplitude dataSet)
      (spatialWeight dataSet domain term)))
    composed

cauchyWeightedDerivativeCompilerLevel : ProofLevel
cauchyWeightedDerivativeCompilerLevel = machineChecked

-- Source/analytic leaf after this compiler:
-- identify the selected two-J derivative with a finite-polydisc Cauchy
-- derivative on one cutoff-uniform common radius, and provide the associated
-- nonnegative inverse-radius cost.  No second spatial localization theorem is
-- needed once the undifferentiated activity already carries the weight.
literalCMP116TwoJCauchyCoordinateAndUniformRadiusLevel : ProofLevel
literalCMP116TwoJCauchyCoordinateAndUniformRadiusLevel = conditional

clayPromotion : Bool
clayPromotion = false

clayPromotionIsFalse : clayPromotion ≡ false
clayPromotionIsFalse = refl
