{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanCMP116FixedPointMetricHessianRound382Exact where

------------------------------------------------------------------------
-- ROUND382 / THE HESSIAN PARAMETER METRIC IS THE R370 FIXED-POINT METRIC
--
-- R381 removed the duplicated R373 selected-distance coordinate, but it still
-- accepted an R372 Hessian record plus a same-object equality saying the R372
-- substitution distance was the R370 boundary fixed-point distance.
--
-- That equality is also avoidable at the preferred direct cut.  The Hessian
-- family is differentiated WITH RESPECT TO the substituted background produced
-- by the R370 fixed-point family.  Therefore instantiate the R372 Cauchy
-- sensitivity authority so that its parameter metric is definitionally the
-- R370 background metric.  Then use R370.boundarySubstitutionDistance itself as
-- R372.sourceSubstitutionDistance.
--
-- The only distance theorem used is the one R370 already owns:
--
--   boundarySubstitutionDistance
--     = backgroundDistance(fixedPoint(left), fixedPoint(right)).
--
-- Hence no second R372<->R370 distance weld remains.  The real source-facing
-- leaves are now the literal Hessian-family/scalar attachment and the common
-- analytic neighbourhood/radius/magnitude needed by Cauchy differentiation.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality using (subst; sym)

open import DASHI.Foundations.RealAnalysisAxioms using
  (ℝ; 0ℝ; _*ℝ_; _≤ℝ_; ≤ℝ-refl)
open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Physics.YangMills.BalabanCMP116DirectParametricSensitivityRound370Exact as R370
import DASHI.Physics.YangMills.BalabanCMP116DirectHessianSensitivityRound372Exact as R372
import DASHI.Physics.YangMills.BalabanCMP116JointParametricSensitivityRound373Exact as R373
import DASHI.Physics.YangMills.BalabanCMP116ParametricDistanceUpperHessianRound380Exact as R380
import DASHI.Physics.YangMills.BalabanCMP116CanonicalR370R373BoundaryRound381Exact as R381

------------------------------------------------------------------------
-- Cauchy sensitivity for Hessian values, explicitly measured in the SAME
-- substituted-background metric already owned by R370.
------------------------------------------------------------------------

record HessianCauchyOnR370FixedPointMetric
    (parametric : R370.CMP116DirectParametricSensitivityData)
    (HessianValue : Set) : Set₁ where
  field
    hessianDistance : HessianValue → HessianValue → ℝ

    AnalyticFamily : (R370.Background parametric → HessianValue) → Set
    UniformMagnitudeBound :
      (R370.Background parametric → HessianValue) → ℝ → Set
    PositiveRadiusMargin : ℝ → Set
    CommonNeighbourhood :
      R370.Background parametric → R370.Background parametric → Set

    lipschitzConstant : ℝ → ℝ → ℝ

    hessianDistanceNonnegative :
      ∀ left right → 0ℝ ≤ℝ hessianDistance left right

    lipschitzTimesUpperNonnegative :
      ∀ magnitude radius upper →
      PositiveRadiusMargin radius →
      0ℝ ≤ℝ upper →
      0ℝ ≤ℝ lipschitzConstant magnitude radius *ℝ upper

    cauchySensitivityWithDistanceUpper :
      ∀ family magnitude radius left right upper →
      AnalyticFamily family →
      UniformMagnitudeBound family magnitude →
      PositiveRadiusMargin radius →
      CommonNeighbourhood left right →
      R370.backgroundDistance (R370.sensitivity parametric) left right ≤ℝ upper →
      hessianDistance (family left) (family right)
        ≤ℝ lipschitzConstant magnitude radius *ℝ upper

open HessianCauchyOnR370FixedPointMetric public

asR372Sensitivity :
  ∀ {parametric HessianValue} →
  HessianCauchyOnR370FixedPointMetric parametric HessianValue →
  R370.CauchyParametricSensitivityAuthority
    (R370.Background parametric) HessianValue
asR372Sensitivity {parametric} authority = record
  { R370.parameterDistance =
      R370.backgroundDistance (R370.sensitivity parametric)
  ; R370.backgroundDistance = hessianDistance authority
  ; R370.AnalyticFamily = AnalyticFamily authority
  ; R370.UniformMagnitudeBound = UniformMagnitudeBound authority
  ; R370.PositiveRadiusMargin = PositiveRadiusMargin authority
  ; R370.CommonNeighbourhood = CommonNeighbourhood authority
  ; R370.lipschitzConstant = lipschitzConstant authority
  ; R370.backgroundDistanceNonnegative = hessianDistanceNonnegative authority
  ; R370.lipschitzTimesUpperNonnegative =
      lipschitzTimesUpperNonnegative authority
  ; R370.cauchySensitivityWithDistanceUpper =
      cauchySensitivityWithDistanceUpper authority
  }

------------------------------------------------------------------------
-- Canonical R372 Hessian application over the literal R370 boundary carrier.
------------------------------------------------------------------------

record FixedPointMetricHessianData : Set₁ where
  field
    parametric : R370.CMP116DirectParametricSensitivityData

    HessianValue : Set
    hessianAuthority :
      HessianCauchyOnR370FixedPointMetric parametric HessianValue

    hessianFamily :
      R380.R370Boundary parametric →
      R370.Background parametric → HessianValue

    sourceMagnitudeBound sourceRadius : ℝ

    sourceHessianAnalytic :
      ∀ s → AnalyticFamily hessianAuthority (hessianFamily s)

    sourceHessianUniformlyBounded :
      ∀ s →
      UniformMagnitudeBound hessianAuthority
        (hessianFamily s) sourceMagnitudeBound

    sourceRadiusPositive :
      PositiveRadiusMargin hessianAuthority sourceRadius

    selectedSubstitutedBackgroundsShareNeighbourhood :
      ∀ s →
      CommonNeighbourhood hessianAuthority
        (R370.fixedPointFamily parametric (R370.boundaryIndex parametric s)
          (R370.leftParameter parametric (R370.boundaryIndex parametric s)))
        (R370.fixedPointFamily parametric (R370.boundaryIndex parametric s)
          (R370.rightParameter parametric (R370.boundaryIndex parametric s)))

    sourceHessianDifference : R380.R370Boundary parametric → ℝ

    sourceHessianDifferenceIsTargetDistance :
      ∀ s →
      sourceHessianDifference s ≡
      hessianDistance hessianAuthority
        (hessianFamily s
          (R370.fixedPointFamily parametric (R370.boundaryIndex parametric s)
            (R370.leftParameter parametric (R370.boundaryIndex parametric s))))
        (hessianFamily s
          (R370.fixedPointFamily parametric (R370.boundaryIndex parametric s)
            (R370.rightParameter parametric (R370.boundaryIndex parametric s))))

    -- Literal selected scalar attachment.  This is the remaining R373
    -- same-object theorem, now independent of any duplicate distance coordinate.
    hessianDifferenceIsBoundaryNorm :
      ∀ s →
      sourceHessianDifference s ≡
      R373.boundaryNormDifference
        (R370.decoupled parametric)
        (R370.leftDomain parametric)
        (R370.rightDomain parametric)
        (R370.component parametric)
        (R370.leftVariation parametric)
        (R370.rightVariation parametric)
        s

    sourceHessianLipschitzNonnegative :
      0ℝ ≤ℝ
      lipschitzConstant hessianAuthority sourceMagnitudeBound sourceRadius

open FixedPointMetricHessianData public

leftFixedPoint :
  (dataSet : FixedPointMetricHessianData) →
  R380.R370Boundary (parametric dataSet) →
  R370.Background (parametric dataSet)
leftFixedPoint dataSet s =
  R370.fixedPointFamily (parametric dataSet)
    (R370.boundaryIndex (parametric dataSet) s)
    (R370.leftParameter (parametric dataSet)
      (R370.boundaryIndex (parametric dataSet) s))

rightFixedPoint :
  (dataSet : FixedPointMetricHessianData) →
  R380.R370Boundary (parametric dataSet) →
  R370.Background (parametric dataSet)
rightFixedPoint dataSet s =
  R370.fixedPointFamily (parametric dataSet)
    (R370.boundaryIndex (parametric dataSet) s)
    (R370.rightParameter (parametric dataSet)
      (R370.boundaryIndex (parametric dataSet) s))

fixedPointMetricBelowBoundaryDistance :
  (dataSet : FixedPointMetricHessianData) →
  ∀ s →
  R370.parameterDistance (asR372Sensitivity (hessianAuthority dataSet))
    (leftFixedPoint dataSet s) (rightFixedPoint dataSet s)
  ≤ℝ R370.boundarySubstitutionDistance (parametric dataSet) s
fixedPointMetricBelowBoundaryDistance dataSet s =
  subst
    (λ distance →
      R370.backgroundDistance (R370.sensitivity (parametric dataSet))
        (leftFixedPoint dataSet s) (rightFixedPoint dataSet s)
      ≤ℝ distance)
    (sym
      (R370.boundarySubstitutionDistanceIsParametricFixedPointDistance
        (parametric dataSet) s))
    ≤ℝ-refl

canonicalHessian :
  FixedPointMetricHessianData →
  R372.CMP116DirectHessianSensitivityData
canonicalHessian dataSet = record
  { R372.SubstitutedBackground = R370.Background (parametric dataSet)
  ; R372.HessianValue = HessianValue dataSet
  ; R372.Boundary = R380.R370Boundary (parametric dataSet)
  ; R372.sensitivity = asR372Sensitivity (hessianAuthority dataSet)
  ; R372.hessianFamily = hessianFamily dataSet
  ; R372.sourceMagnitudeBound = sourceMagnitudeBound dataSet
  ; R372.sourceRadius = sourceRadius dataSet
  ; R372.sourceSubstitutionDistance =
      R370.boundarySubstitutionDistance (parametric dataSet)
  ; R372.sourceSubstitutionDistanceNonnegative =
      R370.boundarySubstitutionDistanceNonnegativeFromParametric
        (parametric dataSet)
  ; R372.sourceHessianAnalytic = sourceHessianAnalytic dataSet
  ; R372.sourceHessianUniformlyBounded = sourceHessianUniformlyBounded dataSet
  ; R372.sourceRadiusPositive = sourceRadiusPositive dataSet
  ; R372.leftSubstituted = leftFixedPoint dataSet
  ; R372.rightSubstituted = rightFixedPoint dataSet
  ; R372.selectedSubstitutedBackgroundsShareNeighbourhood =
      selectedSubstitutedBackgroundsShareNeighbourhood dataSet
  ; R372.selectedSubstitutionDistanceBelowSourceDistance =
      fixedPointMetricBelowBoundaryDistance dataSet
  ; R372.sourceHessianDifference = sourceHessianDifference dataSet
  ; R372.sourceHessianDifferenceIsTargetDistance =
      sourceHessianDifferenceIsTargetDistance dataSet
  }

canonicalR381 :
  (dataSet : FixedPointMetricHessianData) →
  R381.CanonicalR370R373BoundaryData
canonicalR381 dataSet = record
  { R381.parametric = parametric dataSet
  ; R381.hessian = canonicalHessian dataSet
  ; R381.boundaryToHessianBoundary = λ s → s
  ; R381.hessianDifferenceIsBoundaryNorm =
      hessianDifferenceIsBoundaryNorm dataSet
  ; R381.hessianDistanceIsParametricBoundaryDistance = λ s → refl
  }

canonicalR380 :
  (dataSet : FixedPointMetricHessianData) →
  R380.CMP116ParametricDistanceUpperHessianData
canonicalR380 dataSet =
  R381.canonicalRound380
    (canonicalR381 dataSet)
    (sourceHessianLipschitzNonnegative dataSet)

------------------------------------------------------------------------
-- Pareto / authority boundary.
------------------------------------------------------------------------

round382FixedPointMetricHessianCompilerLevel : ProofLevel
round382FixedPointMetricHessianCompilerLevel = machineChecked

separateR372ToR370DistanceWeldRequiredAfterRound382 : Bool
separateR372ToR370DistanceWeldRequiredAfterRound382 = false

separateR372ToR370DistanceWeldRequiredAfterRound382IsFalse :
  separateR372ToR370DistanceWeldRequiredAfterRound382 ≡ false
separateR372ToR370DistanceWeldRequiredAfterRound382IsFalse = refl

separateR373ToR370BoundaryMapRequiredAfterRound382 : Bool
separateR373ToR370BoundaryMapRequiredAfterRound382 = false

separateR373ToR370BoundaryMapRequiredAfterRound382IsFalse :
  separateR373ToR370BoundaryMapRequiredAfterRound382 ≡ false
separateR373ToR370BoundaryMapRequiredAfterRound382IsFalse = refl

literalHessianFamilyAttachmentStillRequired : Bool
literalHessianFamilyAttachmentStillRequired = true

literalHessianFamilyAttachmentStillRequiredIsTrue :
  literalHessianFamilyAttachmentStillRequired ≡ true
literalHessianFamilyAttachmentStillRequiredIsTrue = refl

literalHessianScalarizationStillRequired : Bool
literalHessianScalarizationStillRequired = true

literalHessianScalarizationStillRequiredIsTrue :
  literalHessianScalarizationStillRequired ≡ true
literalHessianScalarizationStillRequiredIsTrue = refl

record Round382Boundary : Set where
  constructor round382-boundary
  field
    hessianUsesExactR370FixedPointMetric : Bool
    hessianUsesExactR370FixedPointMetricIsTrue :
      hessianUsesExactR370FixedPointMetric ≡ true

    r372DistanceCoordinateIsR370DistanceByConstruction : Bool
    r372DistanceCoordinateIsR370DistanceByConstructionIsTrue :
      r372DistanceCoordinateIsR370DistanceByConstruction ≡ true

    sourceFacingAnalyticHessianAttachmentRemains : Bool
    sourceFacingAnalyticHessianAttachmentRemainsIsTrue :
      sourceFacingAnalyticHessianAttachmentRemains ≡ true

canonicalRound382Boundary : Round382Boundary
canonicalRound382Boundary =
  round382-boundary true refl true refl true refl

round382FrontierRefinementLevel : ProofLevel
round382FrontierRefinementLevel = machineChecked

clayPromotion : Bool
clayPromotion = false

clayPromotionIsFalse : clayPromotion ≡ false
