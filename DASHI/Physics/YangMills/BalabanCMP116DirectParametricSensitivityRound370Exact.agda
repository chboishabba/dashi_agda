module DASHI.Physics.YangMills.BalabanCMP116DirectParametricSensitivityRound370Exact where

------------------------------------------------------------------------
-- ROUND370 / DIRECT PARAMETRIC SENSITIVITY OF THE CMP116 FIXED POINT
--
-- R365--R369 expose one valid producer for H_subScale:
--
--   fixed-parameter contraction
--   + cross-parameter C sensitivity
--   + CMP99 H_L-H_R
--   + affine/operator attachment
--   -> one-step map defect -> fixed-point displacement.
--
-- CMP116 Sect. 1 also advertises a logically different producer.  After
-- replacing H by H(s(Y0)), the fixed point D(H(s(Y0)),A') is analytic in the
-- complex decoupling parameters and is uniformly bounded on the declared
-- source domain.  Standard Cauchy + mean-value reasoning can therefore bound
-- the fixed-point displacement directly from parameter displacement, provided
-- the SAME selected parameter segment/disc and source bound are attached.
--
-- This file owns only that compiler boundary.  It does not manufacture the
-- literal CMP116 analytic-family inhabitant, its common parameter disc, its
-- uniform magnitude constant, or the selected-trajectory attachment.  It also
-- does not declare this route cheaper than R366--R369 until those acquisition
-- costs are compared on the same physical carrier.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

open import DASHI.Foundations.RealAnalysisAxioms using
  (ℝ; 0ℝ; _*ℝ_; _≤ℝ_)
import DASHI.Foundations.FinitePolydiscCauchyAxioms as Cauchy
open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Physics.YangMills.BalabanCMP116DifferentiatedLocalizationSourceExact as CMP116
import DASHI.Physics.YangMills.BalabanDecoupledActivityHessian as Decoupled
import DASHI.Physics.YangMills.BalabanDecoupledActivityDirectStabilityRound364Exact as R364

------------------------------------------------------------------------
-- Standard-analysis authority.
--
-- This is deliberately implementation-neutral: Parameter may be a scalar,
-- finite polydisc coordinate, or a selected finite decoupling-parameter fibre.
-- The theorem says what ordinary Cauchy/mean-value analysis contributes once
-- the application supplies an analytic family, uniform bound, positive margin,
-- common neighbourhood, and a parameter-distance upper bound.
------------------------------------------------------------------------

record CauchyParametricSensitivityAuthority
    (Parameter Background : Set) : Set₁ where
  field
    parameterDistance : Parameter → Parameter → ℝ
    backgroundDistance : Background → Background → ℝ

    AnalyticFamily : (Parameter → Background) → Set
    UniformMagnitudeBound : (Parameter → Background) → ℝ → Set
    PositiveRadiusMargin : ℝ → Set
    CommonNeighbourhood : Parameter → Parameter → Set

    lipschitzConstant : ℝ → ℝ → ℝ

    backgroundDistanceNonnegative :
      ∀ left right → 0ℝ ≤ℝ backgroundDistance left right

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
      parameterDistance left right ≤ℝ upper →
      backgroundDistance (family left) (family right)
        ≤ℝ lipschitzConstant magnitude radius *ℝ upper

open CauchyParametricSensitivityAuthority public

------------------------------------------------------------------------
-- Literal CMP116 application into the existing R364 H_subScale ABI.
------------------------------------------------------------------------

record CMP116DirectParametricSensitivityData : Set₁ where
  field
    decoupled : Decoupled.DecoupledActivityHessianData

    leftDomain rightDomain : Decoupled.DomainSequence decoupled
    component : Decoupled.Component decoupled
    leftVariation rightVariation : Decoupled.FieldVariation decoupled

    sourceLipschitz : ℝ
    sourceLipschitzNonnegative : 0ℝ ≤ℝ sourceLipschitz

    Boundary : Set
    boundaryIndex :
      Cauchy.BoundaryAssignment
        (Decoupled.cauchy decoupled)
        (Decoupled.componentIndices decoupled component) → Boundary

    Parameter Background : Set
    sensitivity : CauchyParametricSensitivityAuthority Parameter Background

    fixedPointFamily : Boundary → Parameter → Background
    sourceMagnitudeBound sourceParameterRadius sourceParameterDistance : ℝ
    sourceParameterDistanceNonnegative : 0ℝ ≤ℝ sourceParameterDistance

    sourceFamilyAnalytic :
      ∀ boundary → AnalyticFamily sensitivity (fixedPointFamily boundary)

    sourceFamilyUniformlyBounded :
      ∀ boundary →
      UniformMagnitudeBound sensitivity
        (fixedPointFamily boundary) sourceMagnitudeBound

    sourceParameterRadiusPositive :
      PositiveRadiusMargin sensitivity sourceParameterRadius

    leftParameter rightParameter : Boundary → Parameter

    selectedParametersShareNeighbourhood :
      ∀ boundary →
      CommonNeighbourhood sensitivity
        (leftParameter boundary) (rightParameter boundary)

    selectedParameterDistanceBelowSourceDistance :
      ∀ boundary →
      parameterDistance sensitivity
        (leftParameter boundary) (rightParameter boundary)
      ≤ℝ sourceParameterDistance

    boundarySubstitutionDistance :
      Cauchy.BoundaryAssignment
        (Decoupled.cauchy decoupled)
        (Decoupled.componentIndices decoupled component) → ℝ

    boundarySubstitutionDistanceIsParametricFixedPointDistance :
      ∀ s →
      boundarySubstitutionDistance s ≡
      backgroundDistance sensitivity
        (fixedPointFamily (boundaryIndex s)
          (leftParameter (boundaryIndex s)))
        (fixedPointFamily (boundaryIndex s)
          (rightParameter (boundaryIndex s)))

    -- H_local remains orthogonal to the present H_subScale producer.
    boundaryHessianStable :
      ∀ s →
      Cauchy.normValue (Decoupled.cauchy decoupled)
        (Cauchy._-Value_ (Decoupled.cauchy decoupled)
          (Cauchy.evaluate (Decoupled.cauchy decoupled)
            (Decoupled.asFunction decoupled leftDomain component
              leftVariation rightVariation)
            (Cauchy.boundaryAssignment (Decoupled.cauchy decoupled) s))
          (Cauchy.evaluate (Decoupled.cauchy decoupled)
            (Decoupled.asFunction decoupled rightDomain component
              leftVariation rightVariation)
            (Cauchy.boundaryAssignment (Decoupled.cauchy decoupled) s)))
        ≤ℝ
      sourceLipschitz *ℝ boundarySubstitutionDistance s

open CMP116DirectParametricSensitivityData public

sourceParametricLipschitz : CMP116DirectParametricSensitivityData → ℝ
sourceParametricLipschitz dataSet =
  lipschitzConstant (sensitivity dataSet)
    (sourceMagnitudeBound dataSet)
    (sourceParameterRadius dataSet)

sourceSubstitutionDistance : CMP116DirectParametricSensitivityData → ℝ
sourceSubstitutionDistance dataSet =
  sourceParametricLipschitz dataSet *ℝ sourceParameterDistance dataSet

boundarySubstitutionDistanceNonnegativeFromParametric :
  (dataSet : CMP116DirectParametricSensitivityData) →
  ∀ s → 0ℝ ≤ℝ boundarySubstitutionDistance dataSet s
boundarySubstitutionDistanceNonnegativeFromParametric dataSet s
  rewrite boundarySubstitutionDistanceIsParametricFixedPointDistance dataSet s =
  backgroundDistanceNonnegative (sensitivity dataSet)
    (fixedPointFamily dataSet (boundaryIndex dataSet s)
      (leftParameter dataSet (boundaryIndex dataSet s)))
    (fixedPointFamily dataSet (boundaryIndex dataSet s)
      (rightParameter dataSet (boundaryIndex dataSet s)))

sourceSubstitutionDistanceNonnegativeFromParametric :
  (dataSet : CMP116DirectParametricSensitivityData) →
  0ℝ ≤ℝ sourceSubstitutionDistance dataSet
sourceSubstitutionDistanceNonnegativeFromParametric dataSet =
  lipschitzTimesUpperNonnegative (sensitivity dataSet)
    (sourceMagnitudeBound dataSet)
    (sourceParameterRadius dataSet)
    (sourceParameterDistance dataSet)
    (sourceParameterRadiusPositive dataSet)
    (sourceParameterDistanceNonnegative dataSet)

boundarySubstitutionBelowSourceDistanceFromParametric :
  (dataSet : CMP116DirectParametricSensitivityData) →
  ∀ s →
  boundarySubstitutionDistance dataSet s
    ≤ℝ sourceSubstitutionDistance dataSet
boundarySubstitutionBelowSourceDistanceFromParametric dataSet s
  rewrite boundarySubstitutionDistanceIsParametricFixedPointDistance dataSet s =
  cauchySensitivityWithDistanceUpper (sensitivity dataSet)
    (fixedPointFamily dataSet (boundaryIndex dataSet s))
    (sourceMagnitudeBound dataSet)
    (sourceParameterRadius dataSet)
    (leftParameter dataSet (boundaryIndex dataSet s))
    (rightParameter dataSet (boundaryIndex dataSet s))
    (sourceParameterDistance dataSet)
    (sourceFamilyAnalytic dataSet (boundaryIndex dataSet s))
    (sourceFamilyUniformlyBounded dataSet (boundaryIndex dataSet s))
    (sourceParameterRadiusPositive dataSet)
    (selectedParametersShareNeighbourhood dataSet (boundaryIndex dataSet s))
    (selectedParameterDistanceBelowSourceDistance dataSet (boundaryIndex dataSet s))

round370ToR364 :
  CMP116DirectParametricSensitivityData →
  R364.CMP116DirectSubstitutionStabilityData
round370ToR364 dataSet = record
  { decoupled = decoupled dataSet
  ; leftDomain = leftDomain dataSet
  ; rightDomain = rightDomain dataSet
  ; component = component dataSet
  ; leftVariation = leftVariation dataSet
  ; rightVariation = rightVariation dataSet
  ; sourceLipschitz = sourceLipschitz dataSet
  ; sourceSubstitutionDistance = sourceSubstitutionDistance dataSet
  ; boundarySubstitutionDistance = boundarySubstitutionDistance dataSet
  ; sourceLipschitzNonnegative = sourceLipschitzNonnegative dataSet
  ; boundarySubstitutionDistanceNonnegative =
      boundarySubstitutionDistanceNonnegativeFromParametric dataSet
  ; sourceSubstitutionDistanceNonnegative =
      sourceSubstitutionDistanceNonnegativeFromParametric dataSet
  ; boundaryHessianStable = boundaryHessianStable dataSet
  ; boundarySubstitutionBelowSourceDistance =
      boundarySubstitutionBelowSourceDistanceFromParametric dataSet
  }

------------------------------------------------------------------------
-- Pareto / source accounting.
------------------------------------------------------------------------

standardCauchyParametricSensitivityLevel : ProofLevel
standardCauchyParametricSensitivityLevel = standardImported

cmp116FixedPointAnalyticInDecouplingParametersLevel : ProofLevel
cmp116FixedPointAnalyticInDecouplingParametersLevel = standardImported

cmp116FixedPointUniformSourceBoundLevel : ProofLevel
cmp116FixedPointUniformSourceBoundLevel = standardImported

literalCMP116ParametricFamilySameObjectAttachmentLevel : ProofLevel
literalCMP116ParametricFamilySameObjectAttachmentLevel = conditional

literalCMP116CommonParameterNeighbourhoodLevel : ProofLevel
literalCMP116CommonParameterNeighbourhoodLevel = conditional

literalCMP116ParameterDistanceCalibrationLevel : ProofLevel
literalCMP116ParameterDistanceCalibrationLevel = conditional

round370ToR364CompilerLevel : ProofLevel
round370ToR364CompilerLevel = machineChecked

r366R369PropagatorDefectRouteMandatoryForHSubScale : Bool
r366R369PropagatorDefectRouteMandatoryForHSubScale = false

r366R369PropagatorDefectRouteMandatoryForHSubScaleIsFalse :
  r366R369PropagatorDefectRouteMandatoryForHSubScale ≡ false
r366R369PropagatorDefectRouteMandatoryForHSubScaleIsFalse = refl

r370AutomaticallyCheaperThanPropagatorDefectRoute : Bool
r370AutomaticallyCheaperThanPropagatorDefectRoute = false

r370AutomaticallyCheaperThanPropagatorDefectRouteIsFalse :
  r370AutomaticallyCheaperThanPropagatorDefectRoute ≡ false
r370AutomaticallyCheaperThanPropagatorDefectRouteIsFalse = refl

sourceAnalyticityAlonePaysSelectedSensitivity : Bool
sourceAnalyticityAlonePaysSelectedSensitivity = false

sourceAnalyticityAlonePaysSelectedSensitivityIsFalse :
  sourceAnalyticityAlonePaysSelectedSensitivity ≡ false
sourceAnalyticityAlonePaysSelectedSensitivityIsFalse = refl

record Round370Boundary : Set where
  constructor round370-boundary
  field
    directParametricRouteBypassesCrossParameterC : Bool
    directParametricRouteBypassesCrossParameterCIsTrue :
      directParametricRouteBypassesCrossParameterC ≡ true

    directParametricRouteBypassesCMP99HDefect : Bool
    directParametricRouteBypassesCMP99HDefectIsTrue :
      directParametricRouteBypassesCMP99HDefect ≡ true

    sameObjectParameterFamilyStillRequired : Bool
    sameObjectParameterFamilyStillRequiredIsTrue :
      sameObjectParameterFamilyStillRequired ≡ true

    quantitativeRadiusAndDistanceStillRequired : Bool
    quantitativeRadiusAndDistanceStillRequiredIsTrue :
      quantitativeRadiusAndDistanceStillRequired ≡ true

canonicalRound370Boundary : Round370Boundary
canonicalRound370Boundary =
  round370-boundary true refl true refl true refl true refl

round370FrontierRefinementLevel : ProofLevel
round370FrontierRefinementLevel = machineChecked

clayPromotion : Bool
clayPromotion = false

clayPromotionIsFalse : clayPromotion ≡ false
clayPromotionIsFalse = refl
