{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanCMP116FixedPointToBoundarySubstitutionScaleRound366Exact where

------------------------------------------------------------------------
-- ROUND366 / FIXED-POINT PERTURBATION -> R364-SHAPED H_subScale
--
-- R365 proves pointwise fixed-point stability from contraction + map defect.
-- R364 consumes a boundary-indexed substituted-background distance bounded by
-- one source scale.  This module is the missing generic uniformization compiler:
-- identify each boundary distance with the corresponding pair of fixed points,
-- uniformly majorize the R365 scaled map defect, and obtain H_subScale.
--
-- No literal CMP116 map, contraction, or defect estimate is manufactured here.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Physics.YangMills.BalabanCMP116SubstitutedBackgroundFixedPointStabilityRound365Exact as R365

record UniformBoundaryFixedPointScaleData : Set₁ where
  field
    perturbation : R365.SubstitutedBackgroundFixedPointPerturbationData
    Boundary : Set

    leftParameter rightParameter :
      Boundary → R365.Parameter perturbation

    boundarySubstitutionDistance : Boundary → R365.Bound perturbation
    sourceSubstitutionDistance : R365.Bound perturbation

    boundaryDistanceIsFixedPointDistance : ∀ boundary →
      boundarySubstitutionDistance boundary
      ≡
      R365.distance perturbation
        (R365.fixedPoint perturbation (leftParameter boundary))
        (R365.fixedPoint perturbation (rightParameter boundary))

    -- The only uniform source-specific payment after R365: the scaled
    -- parameter-map defect fits the single distance consumed downstream.
    scaledMapDefectBelowSourceDistance : ∀ boundary →
      R365.LessEqual perturbation
        (R365.scale perturbation
          (R365.stabilityFactor perturbation)
          (R365.mapDefect perturbation
            (leftParameter boundary)
            (rightParameter boundary)))
        sourceSubstitutionDistance

open UniformBoundaryFixedPointScaleData public

boundarySubstitutionBelowSourceDistance :
  (dataSet : UniformBoundaryFixedPointScaleData) →
  ∀ boundary →
  R365.LessEqual (perturbation dataSet)
    (boundarySubstitutionDistance dataSet boundary)
    (sourceSubstitutionDistance dataSet)
boundarySubstitutionBelowSourceDistance dataSet boundary
  rewrite boundaryDistanceIsFixedPointDistance dataSet boundary =
  R365.lessEqualTransitive (perturbation dataSet)
    (R365.fixedPointPerturbationStable
      (perturbation dataSet)
      (leftParameter dataSet boundary)
      (rightParameter dataSet boundary))
    (scaledMapDefectBelowSourceDistance dataSet boundary)

------------------------------------------------------------------------
-- Pareto accounting.
------------------------------------------------------------------------

fixedPointToBoundaryScaleCompilerLevel : ProofLevel
fixedPointToBoundaryScaleCompilerLevel = machineChecked

uniformCMP116MapDefectMajorantLevel : ProofLevel
uniformCMP116MapDefectMajorantLevel = conditional

r364HSubScaleCanBeDerivedFromFixedPointRoute : Bool
r364HSubScaleCanBeDerivedFromFixedPointRoute = true

r364HSubScaleCanBeDerivedFromFixedPointRouteIsTrue :
  r364HSubScaleCanBeDerivedFromFixedPointRoute ≡ true
r364HSubScaleCanBeDerivedFromFixedPointRouteIsTrue = refl

commonAnalyticRadiusAlonePaysHSubScale : Bool
commonAnalyticRadiusAlonePaysHSubScale = false

commonAnalyticRadiusAlonePaysHSubScaleIsFalse :
  commonAnalyticRadiusAlonePaysHSubScale ≡ false
commonAnalyticRadiusAlonePaysHSubScaleIsFalse = refl

clayPromotion : Bool
clayPromotion = false

clayPromotionIsFalse : clayPromotion ≡ false
clayPromotionIsFalse = refl
