{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanCMP116LiteralHessianFamilyRound375Exact where

------------------------------------------------------------------------
-- ROUND375 / THE R372 HESSIAN FAMILY IS ALREADY THE R103 LITERAL FAMILY
--
-- R372 correctly reduced H_local to ordinary parametric Cauchy sensitivity, but
-- its application record still accepted an arbitrary
--
--   hessianFamily : Boundary -> SubstitutedBackground -> HessianValue.
--
-- That is stronger than the live Yang--Mills consumer needs.  Round103 already
-- owns one strict same differentiated CMP109/CMP116 carrier and defines the
-- literal physical marked Hessian on it.  It also proves that this marked
-- Hessian is the CMP109 polarization / second variation of the SAME effective
-- potential.
--
-- This owner therefore fixes the R372 family definitionally to
--
--   background |-> cmp116PhysicalMarkedHessian background u v
--
-- for the selected pair of tangent directions.  No second "identify the
-- Hessian family" theorem is scheduled.  What remains application-specific is
-- quantitative: source magnitude/radius, common-neighbourhood and selected
-- substituted-background distance, plus scalarization into the exact R352
-- consumer.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality using (sym)

open import DASHI.Foundations.RealAnalysisAxioms using (ℝ; 0ℝ; _≤ℝ_)
open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Physics.YangMills.BalabanCMP109116LiteralDifferentiatedCarrierRound103Exact as R103
import DASHI.Physics.YangMills.BalabanCMP109116SourceContinuationRound103Exact as Source
import DASHI.Physics.YangMills.BalabanCMP116DirectParametricSensitivityRound370Exact as R370
import DASHI.Physics.YangMills.BalabanCMP116DirectHessianSensitivityRound372Exact as R372

------------------------------------------------------------------------
-- Literal family, with no free Hessian-object coordinate.
------------------------------------------------------------------------

record CMP116LiteralHessianSensitivityData : Set₁ where
  field
    literal : R103.LiteralDifferentiatedEffectiveDensityCarrier
    Boundary : Set

    leftVariation rightVariation :
      Boundary -> Source.Tangent (R103.source literal)

    sensitivity :
      R370.CauchyParametricSensitivityAuthority
        (Source.Background (R103.source literal)) ℝ

    sourceMagnitudeBound sourceRadius : ℝ

    sourceSubstitutionDistance : Boundary -> ℝ
    sourceSubstitutionDistanceNonnegative :
      forall boundary -> 0ℝ ≤ℝ sourceSubstitutionDistance boundary

    sourceHessianAnalytic :
      forall boundary ->
      R370.AnalyticFamily sensitivity
        (lambda background ->
          R103.cmp116PhysicalMarkedHessian literal background
            (leftVariation boundary) (rightVariation boundary))

    sourceHessianUniformlyBounded :
      forall boundary ->
      R370.UniformMagnitudeBound sensitivity
        (lambda background ->
          R103.cmp116PhysicalMarkedHessian literal background
            (leftVariation boundary) (rightVariation boundary))
        sourceMagnitudeBound

    sourceRadiusPositive :
      R370.PositiveRadiusMargin sensitivity sourceRadius

    leftSubstituted rightSubstituted :
      Boundary -> Source.Background (R103.source literal)

    selectedSubstitutedBackgroundsShareNeighbourhood :
      forall boundary ->
      R370.CommonNeighbourhood sensitivity
        (leftSubstituted boundary) (rightSubstituted boundary)

    selectedSubstitutionDistanceBelowSourceDistance :
      forall boundary ->
      R370.parameterDistance sensitivity
        (leftSubstituted boundary) (rightSubstituted boundary)
      ≤ℝ sourceSubstitutionDistance boundary

    sourceHessianDifference : Boundary -> ℝ
    sourceHessianDifferenceIsTargetDistance :
      forall boundary ->
      sourceHessianDifference boundary ≡
      R370.backgroundDistance sensitivity
        (R103.cmp116PhysicalMarkedHessian literal
          (leftSubstituted boundary)
          (leftVariation boundary) (rightVariation boundary))
        (R103.cmp116PhysicalMarkedHessian literal
          (rightSubstituted boundary)
          (leftVariation boundary) (rightVariation boundary))

open CMP116LiteralHessianSensitivityData public

literalHessianFamily :
  (dataSet : CMP116LiteralHessianSensitivityData) ->
  Boundary dataSet ->
  Source.Background (R103.source (literal dataSet)) -> ℝ
literalHessianFamily dataSet boundary background =
  R103.cmp116PhysicalMarkedHessian
    (literal dataSet) background
    (leftVariation dataSet boundary)
    (rightVariation dataSet boundary)

literalHessianFamilyIsCMP109Polarization :
  (dataSet : CMP116LiteralHessianSensitivityData) ->
  forall boundary background ->
  literalHessianFamily dataSet boundary background ≡
  R103.cmp109Polarization
    (literal dataSet) background
    (leftVariation dataSet boundary)
    (rightVariation dataSet boundary)
literalHessianFamilyIsCMP109Polarization dataSet boundary background =
  sym
    (R103.cmp109PolarizationIsCMP116PhysicalMarkedHessian
      (literal dataSet) background
      (leftVariation dataSet boundary)
      (rightVariation dataSet boundary))

round375ToR372 :
  CMP116LiteralHessianSensitivityData ->
  R372.CMP116DirectHessianSensitivityData
round375ToR372 dataSet = record
  { R372.SubstitutedBackground =
      Source.Background (R103.source (literal dataSet))
  ; R372.HessianValue = ℝ
  ; R372.Boundary = Boundary dataSet
  ; R372.sensitivity = sensitivity dataSet
  ; R372.hessianFamily = literalHessianFamily dataSet
  ; R372.sourceMagnitudeBound = sourceMagnitudeBound dataSet
  ; R372.sourceRadius = sourceRadius dataSet
  ; R372.sourceSubstitutionDistance = sourceSubstitutionDistance dataSet
  ; R372.sourceSubstitutionDistanceNonnegative =
      sourceSubstitutionDistanceNonnegative dataSet
  ; R372.sourceHessianAnalytic = sourceHessianAnalytic dataSet
  ; R372.sourceHessianUniformlyBounded = sourceHessianUniformlyBounded dataSet
  ; R372.sourceRadiusPositive = sourceRadiusPositive dataSet
  ; R372.leftSubstituted = leftSubstituted dataSet
  ; R372.rightSubstituted = rightSubstituted dataSet
  ; R372.selectedSubstitutedBackgroundsShareNeighbourhood =
      selectedSubstitutedBackgroundsShareNeighbourhood dataSet
  ; R372.selectedSubstitutionDistanceBelowSourceDistance =
      selectedSubstitutionDistanceBelowSourceDistance dataSet
  ; R372.sourceHessianDifference = sourceHessianDifference dataSet
  ; R372.sourceHessianDifferenceIsTargetDistance =
      sourceHessianDifferenceIsTargetDistance dataSet
  }

sourceHessianStableFromLiteralCarrier :
  (dataSet : CMP116LiteralHessianSensitivityData) ->
  forall boundary ->
  sourceHessianDifference dataSet boundary
    ≤ℝ
  R372.sourceHessianLipschitz (round375ToR372 dataSet)
    R372.*ℝ
  sourceSubstitutionDistance dataSet boundary
sourceHessianStableFromLiteralCarrier dataSet =
  R372.sourceHessianStableFromCauchy (round375ToR372 dataSet)

------------------------------------------------------------------------
-- Pareto / authority boundary.
------------------------------------------------------------------------

literalSameDifferentiatedCarrierLevel : ProofLevel
literalSameDifferentiatedCarrierLevel = R103.literalDifferentiatedCarrierAssemblyLevel

literalCMP109CMP116HessianIdentityLevel : ProofLevel
literalCMP109CMP116HessianIdentityLevel = R103.cmp109CMP116PhysicalHessianIdentityLevel

r375ToR372CompilerLevel : ProofLevel
r375ToR372CompilerLevel = machineChecked

literalSelectedHessianFamilyIdentityPrimitiveAfterRound375 : Bool
literalSelectedHessianFamilyIdentityPrimitiveAfterRound375 = false

literalSelectedHessianFamilyIdentityPrimitiveAfterRound375IsFalse :
  literalSelectedHessianFamilyIdentityPrimitiveAfterRound375 ≡ false
literalSelectedHessianFamilyIdentityPrimitiveAfterRound375IsFalse = refl

sourceMagnitudeCalibrationStillRequired : Bool
sourceMagnitudeCalibrationStillRequired = true

sourceMagnitudeCalibrationStillRequiredIsTrue :
  sourceMagnitudeCalibrationStillRequired ≡ true
sourceMagnitudeCalibrationStillRequiredIsTrue = refl

selectedSubstitutedBackgroundDistanceStillRequired : Bool
selectedSubstitutedBackgroundDistanceStillRequired = true

selectedSubstitutedBackgroundDistanceStillRequiredIsTrue :
  selectedSubstitutedBackgroundDistanceStillRequired ≡ true
selectedSubstitutedBackgroundDistanceStillRequiredIsTrue = refl

record Round375Boundary : Set where
  constructor round375-boundary
  field
    r103LiteralHessianFamilyFeedsR372 : Bool
    r103LiteralHessianFamilyFeedsR372IsTrue :
      r103LiteralHessianFamilyFeedsR372 ≡ true

    secondFreeHessianFamilyCoordinateRequired : Bool
    secondFreeHessianFamilyCoordinateRequiredIsFalse :
      secondFreeHessianFamilyCoordinateRequired ≡ false

    quantitativeCauchyCalibrationStillRequired : Bool
    quantitativeCauchyCalibrationStillRequiredIsTrue :
      quantitativeCauchyCalibrationStillRequired ≡ true

canonicalRound375Boundary : Round375Boundary
canonicalRound375Boundary =
  round375-boundary true refl false refl true refl

round375FrontierRefinementLevel : ProofLevel
round375FrontierRefinementLevel = machineChecked

clayPromotion : Bool
clayPromotion = false

clayPromotionIsFalse : clayPromotion ≡ false
clayPromotionIsFalse = refl
