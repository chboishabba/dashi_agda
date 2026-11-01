{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanCMP116LiteralFixedPointMetricHessianRound383Exact where

------------------------------------------------------------------------
-- ROUND383 / LITERAL R103 HESSIAN ON THE R370 FIXED-POINT METRIC
--
-- R382 removed the duplicate R372/R370 distance coordinate by measuring the
-- Hessian Cauchy family in the exact R370 fixed-point-output metric.  Its generic
-- compiler still allows an arbitrary Hessian family and arbitrary scalar
-- difference.
--
-- Round375 already identified the physical family: the selected Hessian is the
-- R103 literal CMP116 marked Hessian.  This owner specializes R382 to that
-- family and chooses the scalar difference to BE the exact R373 boundary norm.
-- Therefore two more representation coordinates disappear by construction:
--
--   * no free Hessian-family identity;
--   * no separate Hessian-difference = boundary-norm weld.
--
-- The one surviving scalarization theorem is the genuine same-object statement
--
--   R373 boundary norm
--     = target-space distance between the two literal R103 Hessian values.
--
-- Analyticity, uniform magnitude, positive radius and common-neighbourhood
-- payments remain source/application inputs.  No such estimate is manufactured
-- here.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

open import DASHI.Foundations.RealAnalysisAxioms using (ℝ; 0ℝ; _≤ℝ_)
open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Physics.YangMills.BalabanCMP109116LiteralDifferentiatedCarrierRound103Exact as R103
import DASHI.Physics.YangMills.BalabanCMP109116SourceContinuationRound103Exact as Source
import DASHI.Physics.YangMills.BalabanCMP116DirectParametricSensitivityRound370Exact as R370
import DASHI.Physics.YangMills.BalabanCMP116JointParametricSensitivityRound373Exact as R373
import DASHI.Physics.YangMills.BalabanCMP116ParametricDistanceUpperHessianRound380Exact as R380
import DASHI.Physics.YangMills.BalabanCMP116FixedPointMetricHessianRound382Exact as R382

record LiteralFixedPointMetricHessianData : Set₁ where
  field
    parametric : R370.CMP116DirectParametricSensitivityData
    literal : R103.LiteralDifferentiatedEffectiveDensityCarrier

    -- Application-level carrier map.  In the strongest same-carrier
    -- instantiation this may itself be identity/refl; this module does not assume
    -- that before the source attachment is paid.
    toLiteralBackground :
      R370.Background parametric →
      Source.Background (R103.source literal)

    leftVariation rightVariation :
      R380.R370Boundary parametric →
      Source.Tangent (R103.source literal)

    hessianAuthority :
      R382.HessianCauchyOnR370FixedPointMetric parametric ℝ

    sourceMagnitudeBound sourceRadius : ℝ

    sourceHessianAnalytic :
      ∀ s →
      R382.AnalyticFamily hessianAuthority
        (λ background →
          R103.cmp116PhysicalMarkedHessian literal
            (toLiteralBackground background)
            (leftVariation s) (rightVariation s))

    sourceHessianUniformlyBounded :
      ∀ s →
      R382.UniformMagnitudeBound hessianAuthority
        (λ background →
          R103.cmp116PhysicalMarkedHessian literal
            (toLiteralBackground background)
            (leftVariation s) (rightVariation s))
        sourceMagnitudeBound

    sourceRadiusPositive :
      R382.PositiveRadiusMargin hessianAuthority sourceRadius

    selectedSubstitutedBackgroundsShareNeighbourhood :
      ∀ s →
      R382.CommonNeighbourhood hessianAuthority
        (R370.fixedPointFamily parametric
          (R370.boundaryIndex parametric s)
          (R370.leftParameter parametric
            (R370.boundaryIndex parametric s)))
        (R370.fixedPointFamily parametric
          (R370.boundaryIndex parametric s)
          (R370.rightParameter parametric
            (R370.boundaryIndex parametric s)))

    -- The only scalar same-object weld left by this specialization.
    boundaryNormIsLiteralHessianTargetDistance :
      ∀ s →
      R373.boundaryNormDifference
        (R370.decoupled parametric)
        (R370.leftDomain parametric)
        (R370.rightDomain parametric)
        (R370.component parametric)
        (R370.leftVariation parametric)
        (R370.rightVariation parametric)
        s
      ≡
      R382.hessianDistance hessianAuthority
        (R103.cmp116PhysicalMarkedHessian literal
          (toLiteralBackground
            (R370.fixedPointFamily parametric
              (R370.boundaryIndex parametric s)
              (R370.leftParameter parametric
                (R370.boundaryIndex parametric s))))
          (leftVariation s) (rightVariation s))
        (R103.cmp116PhysicalMarkedHessian literal
          (toLiteralBackground
            (R370.fixedPointFamily parametric
              (R370.boundaryIndex parametric s)
              (R370.rightParameter parametric
                (R370.boundaryIndex parametric s))))
          (leftVariation s) (rightVariation s))

    sourceHessianLipschitzNonnegative :
      0ℝ ≤ℝ
      R382.lipschitzConstant hessianAuthority sourceMagnitudeBound sourceRadius

open LiteralFixedPointMetricHessianData public

asRound382 :
  LiteralFixedPointMetricHessianData →
  R382.FixedPointMetricHessianData
asRound382 dataSet = record
  { R382.parametric = parametric dataSet
  ; R382.HessianValue = ℝ
  ; R382.hessianAuthority = hessianAuthority dataSet
  ; R382.hessianFamily =
      λ s background →
        R103.cmp116PhysicalMarkedHessian
          (literal dataSet)
          (toLiteralBackground dataSet background)
          (leftVariation dataSet s)
          (rightVariation dataSet s)
  ; R382.sourceMagnitudeBound = sourceMagnitudeBound dataSet
  ; R382.sourceRadius = sourceRadius dataSet
  ; R382.sourceHessianAnalytic = sourceHessianAnalytic dataSet
  ; R382.sourceHessianUniformlyBounded = sourceHessianUniformlyBounded dataSet
  ; R382.sourceRadiusPositive = sourceRadiusPositive dataSet
  ; R382.selectedSubstitutedBackgroundsShareNeighbourhood =
      selectedSubstitutedBackgroundsShareNeighbourhood dataSet
  ; R382.sourceHessianDifference =
      λ s →
        R373.boundaryNormDifference
          (R370.decoupled (parametric dataSet))
          (R370.leftDomain (parametric dataSet))
          (R370.rightDomain (parametric dataSet))
          (R370.component (parametric dataSet))
          (R370.leftVariation (parametric dataSet))
          (R370.rightVariation (parametric dataSet))
          s
  ; R382.sourceHessianDifferenceIsTargetDistance =
      boundaryNormIsLiteralHessianTargetDistance dataSet
  ; R382.hessianDifferenceIsBoundaryNorm = λ s → refl
  ; R382.sourceHessianLipschitzNonnegative =
      sourceHessianLipschitzNonnegative dataSet
  }

literalFamilyIsR103MarkedHessian :
  (dataSet : LiteralFixedPointMetricHessianData) →
  ∀ s background →
  R382.hessianFamily (asRound382 dataSet) s background
  ≡
  R103.cmp116PhysicalMarkedHessian
    (literal dataSet)
    (toLiteralBackground dataSet background)
    (leftVariation dataSet s)
    (rightVariation dataSet s)
literalFamilyIsR103MarkedHessian dataSet s background = refl

boundaryDifferenceIsChosenScalar :
  (dataSet : LiteralFixedPointMetricHessianData) →
  ∀ s →
  R382.sourceHessianDifference (asRound382 dataSet) s
  ≡
  R373.boundaryNormDifference
    (R370.decoupled (parametric dataSet))
    (R370.leftDomain (parametric dataSet))
    (R370.rightDomain (parametric dataSet))
    (R370.component (parametric dataSet))
    (R370.leftVariation (parametric dataSet))
    (R370.rightVariation (parametric dataSet))
    s
boundaryDifferenceIsChosenScalar dataSet s = refl

------------------------------------------------------------------------
-- Pareto / authority boundary.
------------------------------------------------------------------------

round383LiteralFixedPointMetricCompilerLevel : ProofLevel
round383LiteralFixedPointMetricCompilerLevel = machineChecked

freeHessianFamilyCoordinateRequiredAfterRound383 : Bool
freeHessianFamilyCoordinateRequiredAfterRound383 = false

freeHessianFamilyCoordinateRequiredAfterRound383IsFalse :
  freeHessianFamilyCoordinateRequiredAfterRound383 ≡ false
freeHessianFamilyCoordinateRequiredAfterRound383IsFalse = refl

separateBoundaryDifferenceCoordinateRequiredAfterRound383 : Bool
separateBoundaryDifferenceCoordinateRequiredAfterRound383 = false

separateBoundaryDifferenceCoordinateRequiredAfterRound383IsFalse :
  separateBoundaryDifferenceCoordinateRequiredAfterRound383 ≡ false
separateBoundaryDifferenceCoordinateRequiredAfterRound383IsFalse = refl

literalBoundaryNormToHessianTargetDistanceStillRequired : Bool
literalBoundaryNormToHessianTargetDistanceStillRequired = true

literalBoundaryNormToHessianTargetDistanceStillRequiredIsTrue :
  literalBoundaryNormToHessianTargetDistanceStillRequired ≡ true
literalBoundaryNormToHessianTargetDistanceStillRequiredIsTrue = refl

record Round383Boundary : Set where
  constructor round383-boundary
  field
    literalR103HessianIsTheOnlyHessianFamily : Bool
    literalR103HessianIsTheOnlyHessianFamilyIsTrue :
      literalR103HessianIsTheOnlyHessianFamily ≡ true

    r373BoundaryNormIsTheOnlyDifferenceScalar : Bool
    r373BoundaryNormIsTheOnlyDifferenceScalarIsTrue :
      r373BoundaryNormIsTheOnlyDifferenceScalar ≡ true

    scalarizationRemainsProofBearing : Bool
    scalarizationRemainsProofBearingIsTrue :
      scalarizationRemainsProofBearing ≡ true

canonicalRound383Boundary : Round383Boundary
canonicalRound383Boundary =
  round383-boundary true refl true refl true refl

round383FrontierRefinementLevel : ProofLevel
round383FrontierRefinementLevel = machineChecked

clayPromotion : Bool
clayPromotion = false

clayPromotionIsFalse : clayPromotion ≡ false
