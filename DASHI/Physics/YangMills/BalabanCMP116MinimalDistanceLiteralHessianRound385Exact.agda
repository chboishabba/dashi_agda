{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanCMP116MinimalDistanceLiteralHessianRound385Exact where

------------------------------------------------------------------------
-- ROUND385 / MINIMAL FIXED-POINT DISTANCE + LITERAL HESSIAN -> R379
--
-- R384 removes the historical H_local socket from the fixed-point-distance
-- producer.  R375/R103 already identify the physical Hessian family.  Therefore
-- the preferred coefficient route need not construct the compatibility chain
-- R370 -> R380 -> R381 -> R382 -> R383 at all.
--
-- This owner composes the two genuinely independent producers at their smallest
-- common coordinate:
--
--   R384:  selected fixed-point distance <= U_par
--   R103:  literal CMP116 marked Hessian family
--
-- and uses ordinary Cauchy sensitivity of that literal Hessian family with the
-- SAME fixed-point-output metric.  The result feeds R379 directly.
--
-- There is no equality asserting that the fixed-point Lipschitz constant equals
-- the Hessian Lipschitz constant.  There is no historical marked-input scalar.
-- There is no duplicate selected-distance coordinate.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality using (subst; sym)

open import DASHI.Foundations.RealAnalysisAxioms using
  (ℝ; 0ℝ; _*ℝ_; _≤ℝ_; ≤ℝ-refl)
import DASHI.Foundations.FinitePolydiscCauchyAxioms as Cauchy
open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Physics.YangMills.BalabanDecoupledActivityHessian as Decoupled
import DASHI.Physics.YangMills.BalabanCMP109116LiteralDifferentiatedCarrierRound103Exact as R103
import DASHI.Physics.YangMills.BalabanCMP109116SourceContinuationRound103Exact as Source
import DASHI.Physics.YangMills.BalabanCMP116DirectParametricSensitivityRound370Exact as R370
import DASHI.Physics.YangMills.BalabanCMP116DirectHessianSensitivityRound372Exact as R372
import DASHI.Physics.YangMills.BalabanCMP116JointParametricSensitivityRound373Exact as R373
import DASHI.Physics.YangMills.BalabanCMP116DistanceUpperHessianBidiRound379Exact as R379
import DASHI.Physics.YangMills.BalabanCMP116MinimalFixedPointDistanceRound384Exact as R384

------------------------------------------------------------------------
-- Hessian Cauchy authority whose parameter metric is definitionally the
-- fixed-point output metric selected by R384.
------------------------------------------------------------------------

record LiteralHessianCauchyOnMinimalMetric
    (distance : R384.CMP116MinimalFixedPointDistanceData) : Set₁ where
  field
    hessianDistance : ℝ → ℝ → ℝ

    AnalyticFamily : (R384.Background distance → ℝ) → Set
    UniformMagnitudeBound : (R384.Background distance → ℝ) → ℝ → Set
    PositiveRadiusMargin : ℝ → Set
    CommonNeighbourhood :
      R384.Background distance → R384.Background distance → Set

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
      R370.backgroundDistance (R384.sensitivity distance) left right ≤ℝ upper →
      hessianDistance (family left) (family right)
        ≤ℝ lipschitzConstant magnitude radius *ℝ upper

open LiteralHessianCauchyOnMinimalMetric public

asR372Sensitivity :
  ∀ {distance} →
  LiteralHessianCauchyOnMinimalMetric distance →
  R370.CauchyParametricSensitivityAuthority (R384.Background distance) ℝ
asR372Sensitivity {distance} authority = record
  { R370.parameterDistance =
      R370.backgroundDistance (R384.sensitivity distance)
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
-- Literal physical specialization.
------------------------------------------------------------------------

R384Boundary : R384.CMP116MinimalFixedPointDistanceData → Set
R384Boundary distance =
  Cauchy.BoundaryAssignment
    (Decoupled.cauchy (R384.decoupled distance))
    (Decoupled.componentIndices
      (R384.decoupled distance)
      (R384.component distance))

leftFixedPoint :
  (distance : R384.CMP116MinimalFixedPointDistanceData) →
  R384Boundary distance → R384.Background distance
leftFixedPoint distance s =
  R384.fixedPointFamily distance (R384.boundaryIndex distance s)
    (R384.leftParameter distance (R384.boundaryIndex distance s))

rightFixedPoint :
  (distance : R384.CMP116MinimalFixedPointDistanceData) →
  R384Boundary distance → R384.Background distance
rightFixedPoint distance s =
  R384.fixedPointFamily distance (R384.boundaryIndex distance s)
    (R384.rightParameter distance (R384.boundaryIndex distance s))

record MinimalDistanceLiteralHessianData : Set₁ where
  field
    distance : R384.CMP116MinimalFixedPointDistanceData

    leftDomain rightDomain :
      Decoupled.DomainSequence (R384.decoupled distance)
    leftVariation rightVariation :
      Decoupled.FieldVariation (R384.decoupled distance)

    literal : R103.LiteralDifferentiatedEffectiveDensityCarrier
    toLiteralBackground :
      R384.Background distance → Source.Background (R103.source literal)

    literalLeftTangent literalRightTangent :
      R384Boundary distance → Source.Tangent (R103.source literal)

    hessianAuthority : LiteralHessianCauchyOnMinimalMetric distance

    sourceMagnitudeBound sourceRadius : ℝ

    sourceHessianAnalytic :
      ∀ s →
      AnalyticFamily hessianAuthority
        (λ background →
          R103.cmp116PhysicalMarkedHessian literal
            (toLiteralBackground background)
            (literalLeftTangent s) (literalRightTangent s))

    sourceHessianUniformlyBounded :
      ∀ s →
      UniformMagnitudeBound hessianAuthority
        (λ background →
          R103.cmp116PhysicalMarkedHessian literal
            (toLiteralBackground background)
            (literalLeftTangent s) (literalRightTangent s))
        sourceMagnitudeBound

    sourceRadiusPositive : PositiveRadiusMargin hessianAuthority sourceRadius

    selectedFixedPointsShareNeighbourhood :
      ∀ s →
      CommonNeighbourhood hessianAuthority
        (leftFixedPoint distance s) (rightFixedPoint distance s)

    -- This is now the one literal scalar same-object weld in the local
    -- coefficient lane: the old Decoupled boundary scalar is exactly the target
    -- distance between the two R103 physical marked-Hessian values.
    boundaryNormIsLiteralHessianTargetDistance :
      ∀ s →
      R373.boundaryNormDifference
        (R384.decoupled distance)
        leftDomain rightDomain
        (R384.component distance)
        leftVariation rightVariation s
      ≡
      hessianDistance hessianAuthority
        (R103.cmp116PhysicalMarkedHessian literal
          (toLiteralBackground (leftFixedPoint distance s))
          (literalLeftTangent s) (literalRightTangent s))
        (R103.cmp116PhysicalMarkedHessian literal
          (toLiteralBackground (rightFixedPoint distance s))
          (literalLeftTangent s) (literalRightTangent s))

    hessianLipschitzNonnegative :
      0ℝ ≤ℝ lipschitzConstant hessianAuthority sourceMagnitudeBound sourceRadius

open MinimalDistanceLiteralHessianData public

fixedPointMetricBelowSelectedDistance :
  (dataSet : MinimalDistanceLiteralHessianData) →
  ∀ s →
  R370.parameterDistance (asR372Sensitivity (hessianAuthority dataSet))
    (leftFixedPoint (distance dataSet) s)
    (rightFixedPoint (distance dataSet) s)
  ≤ℝ R384.boundarySubstitutionDistance (distance dataSet) s
fixedPointMetricBelowSelectedDistance dataSet s =
  subst
    (λ upper →
      R370.backgroundDistance (R384.sensitivity (distance dataSet))
        (leftFixedPoint (distance dataSet) s)
        (rightFixedPoint (distance dataSet) s)
      ≤ℝ upper)
    (sym
      (R384.boundarySubstitutionDistanceIsParametricFixedPointDistance
        (distance dataSet) s))
    ≤ℝ-refl

canonicalHessian :
  (dataSet : MinimalDistanceLiteralHessianData) →
  R372.CMP116DirectHessianSensitivityData
canonicalHessian dataSet = record
  { R372.SubstitutedBackground = R384.Background (distance dataSet)
  ; R372.HessianValue = ℝ
  ; R372.Boundary = R384Boundary (distance dataSet)
  ; R372.sensitivity = asR372Sensitivity (hessianAuthority dataSet)
  ; R372.hessianFamily =
      λ s background →
        R103.cmp116PhysicalMarkedHessian
          (literal dataSet)
          (toLiteralBackground dataSet background)
          (literalLeftTangent dataSet s)
          (literalRightTangent dataSet s)
  ; R372.sourceMagnitudeBound = sourceMagnitudeBound dataSet
  ; R372.sourceRadius = sourceRadius dataSet
  ; R372.sourceSubstitutionDistance =
      R384.boundarySubstitutionDistance (distance dataSet)
  ; R372.sourceSubstitutionDistanceNonnegative =
      R384.boundaryDistanceNonnegative (distance dataSet)
  ; R372.sourceHessianAnalytic = sourceHessianAnalytic dataSet
  ; R372.sourceHessianUniformlyBounded = sourceHessianUniformlyBounded dataSet
  ; R372.sourceRadiusPositive = sourceRadiusPositive dataSet
  ; R372.leftSubstituted = leftFixedPoint (distance dataSet)
  ; R372.rightSubstituted = rightFixedPoint (distance dataSet)
  ; R372.selectedSubstitutedBackgroundsShareNeighbourhood =
      selectedFixedPointsShareNeighbourhood dataSet
  ; R372.selectedSubstitutionDistanceBelowSourceDistance =
      fixedPointMetricBelowSelectedDistance dataSet
  ; R372.sourceHessianDifference =
      λ s →
        R373.boundaryNormDifference
          (R384.decoupled (distance dataSet))
          (leftDomain dataSet) (rightDomain dataSet)
          (R384.component (distance dataSet))
          (leftVariation dataSet) (rightVariation dataSet) s
  ; R372.sourceHessianDifferenceIsTargetDistance =
      boundaryNormIsLiteralHessianTargetDistance dataSet
  }

canonicalJoint :
  (dataSet : MinimalDistanceLiteralHessianData) →
  R373.JointBoundaryHessianPaymentData
canonicalJoint dataSet = record
  { R373.decoupled = R384.decoupled (distance dataSet)
  ; R373.leftDomain = leftDomain dataSet
  ; R373.rightDomain = rightDomain dataSet
  ; R373.component = R384.component (distance dataSet)
  ; R373.leftVariation = leftVariation dataSet
  ; R373.rightVariation = rightVariation dataSet
  ; R373.selectedLipschitz =
      R372.sourceHessianLipschitz (canonicalHessian dataSet)
  ; R373.selectedBoundarySubstitutionDistance =
      R384.boundarySubstitutionDistance (distance dataSet)
  ; R373.hessian = canonicalHessian dataSet
  ; R373.boundaryToHessianBoundary = λ s → s
  ; R373.hessianDifferenceIsBoundaryNorm = λ s → refl
  ; R373.hessianLipschitzIsSelectedLipschitz = refl
  ; R373.hessianDistanceIsSelectedBoundaryDistance = λ s → refl
  }

asRound379 :
  (dataSet : MinimalDistanceLiteralHessianData) →
  R379.CMP116DistanceUpperHessianBidiData
asRound379 dataSet = record
  { R379.joint = canonicalJoint dataSet
  ; R379.distanceUpper = R384.distanceUpper (distance dataSet)
  ; R379.distanceUpperNonnegative =
      R384.distanceUpperNonnegative (distance dataSet)
  ; R379.selectedBoundaryDistanceNonnegative =
      R384.boundaryDistanceNonnegative (distance dataSet)
  ; R379.selectedLipschitzNonnegative = hessianLipschitzNonnegative dataSet
  ; R379.selectedBoundaryDistanceBelowUpper =
      R384.boundaryDistanceBelowUpper (distance dataSet)
  }

selectedCoefficientDifferenceFromMinimalProducers :
  (dataSet : MinimalDistanceLiteralHessianData) →
  Cauchy.normValue
    (Decoupled.cauchy (R384.decoupled (distance dataSet)))
    (Cauchy._-Value_
      (Decoupled.cauchy (R384.decoupled (distance dataSet)))
      (Decoupled.decoupledHessianCoefficient
        (R384.decoupled (distance dataSet))
        (leftDomain dataSet)
        (R384.component (distance dataSet))
        (leftVariation dataSet) (rightVariation dataSet))
      (Decoupled.decoupledHessianCoefficient
        (R384.decoupled (distance dataSet))
        (rightDomain dataSet)
        (R384.component (distance dataSet))
        (leftVariation dataSet) (rightVariation dataSet)))
  ≤ℝ
  R372.sourceHessianLipschitz (canonicalHessian dataSet) *ℝ
    R384.distanceUpper (distance dataSet)
selectedCoefficientDifferenceFromMinimalProducers dataSet =
  R379.selectedCoefficientDifferenceBelowDistanceUpper (asRound379 dataSet)

------------------------------------------------------------------------
-- Pareto / authority boundary.
------------------------------------------------------------------------

round385DirectMinimalCompositionLevel : ProofLevel
round385DirectMinimalCompositionLevel = machineChecked

fullR370RecordMandatoryForCoefficientAfterRound385 : Bool
fullR370RecordMandatoryForCoefficientAfterRound385 = false

fullR370RecordMandatoryForCoefficientAfterRound385IsFalse :
  fullR370RecordMandatoryForCoefficientAfterRound385 ≡ false
fullR370RecordMandatoryForCoefficientAfterRound385IsFalse = refl

round380Round383CompatibilityChainMandatoryAfterRound385 : Bool
round380Round383CompatibilityChainMandatoryAfterRound385 = false

round380Round383CompatibilityChainMandatoryAfterRound385IsFalse :
  round380Round383CompatibilityChainMandatoryAfterRound385 ≡ false
round380Round383CompatibilityChainMandatoryAfterRound385IsFalse = refl

historicalMarkedInputMandatoryAfterRound385 : Bool
historicalMarkedInputMandatoryAfterRound385 = false

historicalMarkedInputMandatoryAfterRound385IsFalse :
  historicalMarkedInputMandatoryAfterRound385 ≡ false
historicalMarkedInputMandatoryAfterRound385IsFalse = refl

fixedPointAndHessianLipschitzConstantsMustCoincide : Bool
fixedPointAndHessianLipschitzConstantsMustCoincide = false

fixedPointAndHessianLipschitzConstantsMustCoincideIsFalse :
  fixedPointAndHessianLipschitzConstantsMustCoincide ≡ false
fixedPointAndHessianLipschitzConstantsMustCoincideIsFalse = refl

literalBoundaryNormScalarizationStillRequired : Bool
literalBoundaryNormScalarizationStillRequired = true

literalBoundaryNormScalarizationStillRequiredIsTrue :
  literalBoundaryNormScalarizationStillRequired ≡ true
literalBoundaryNormScalarizationStillRequiredIsTrue = refl

record Round385Boundary : Set where
  constructor round385-boundary
  field
    fixedPointDistanceProducerIndependentOfHessian : Bool
    fixedPointDistanceProducerIndependentOfHessianIsTrue :
      fixedPointDistanceProducerIndependentOfHessian ≡ true

    literalHessianMeetsDistanceOnlyAtSelectedMetric : Bool
    literalHessianMeetsDistanceOnlyAtSelectedMetricIsTrue :
      literalHessianMeetsDistanceOnlyAtSelectedMetric ≡ true

    r379ConsumesTwoMinimalProducersDirectly : Bool
    r379ConsumesTwoMinimalProducersDirectlyIsTrue :
      r379ConsumesTwoMinimalProducersDirectly ≡ true

canonicalRound385Boundary : Round385Boundary
canonicalRound385Boundary =
  round385-boundary true refl true refl true refl

round385FrontierRefinementLevel : ProofLevel
round385FrontierRefinementLevel = machineChecked

clayPromotion : Bool
clayPromotion = false

clayPromotionIsFalse : clayPromotion ≡ false
