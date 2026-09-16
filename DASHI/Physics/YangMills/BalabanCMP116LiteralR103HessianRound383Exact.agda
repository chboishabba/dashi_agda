module DASHI.Physics.YangMills.BalabanCMP116LiteralR103HessianRound383Exact where

------------------------------------------------------------------------
-- ROUND383 / SPECIALIZE THE GENERIC R372 HESSIAN FAMILY TO LITERAL R103
--
-- R372 intentionally accepts an abstract selected Hessian family.  But the
-- repository already owns the exact differentiated CMP109/CMP116 carrier in
-- Round103:
--
--   cmp116PhysicalMarkedHessian
--     = cmp109Polarization
--     = D²(effectivePotential)
--
-- on one literal source/calculus/scale/volume carrier.
--
-- This adapter chooses the R372 Hessian family to be that existing literal
-- function by construction.  It also chooses R372's auxiliary
-- `sourceHessianDifference` to be the target-space distance itself, so the old
-- free difference coordinate disappears.
--
-- Nothing analytic is manufactured here.  The application still supplies:
--   * Cauchy/mean-value authority on the selected background carrier;
--   * analyticity and uniform magnitude of the literal R103 Hessian family;
--   * positive radius margin and common neighbourhood;
--   * selected left/right substituted backgrounds;
--   * a proof-bearing parameter-distance upper.
--
-- Thus this is SAME_OBJECT_TRANSPORT / compiler plumbing only.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

open import DASHI.Foundations.RealAnalysisAxioms using (ℝ; 0ℝ; _≤ℝ_)
open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Physics.YangMills.BalabanCMP109116SourceContinuationRound103Exact as Source
import DASHI.Physics.YangMills.BalabanCMP109116LiteralDifferentiatedCarrierRound103Exact as R103
import DASHI.Physics.YangMills.BalabanCMP116DirectParametricSensitivityRound370Exact as R370
import DASHI.Physics.YangMills.BalabanCMP116DirectHessianSensitivityRound372Exact as R372

------------------------------------------------------------------------
-- Literal selected R103 application.
------------------------------------------------------------------------

record LiteralR103HessianSensitivityData
    (literal : R103.LiteralDifferentiatedEffectiveDensityCarrier) : Set₁ where
  field
    Boundary : Set

    leftVariation rightVariation :
      Boundary → Source.Tangent (R103.source literal)

    sensitivity :
      R370.CauchyParametricSensitivityAuthority
        (Source.Background (R103.source literal)) ℝ

    sourceMagnitudeBound sourceRadius : ℝ

    sourceSubstitutionDistance : Boundary → ℝ
    sourceSubstitutionDistanceNonnegative :
      ∀ boundary → 0ℝ ≤ℝ sourceSubstitutionDistance boundary

    sourceHessianAnalytic :
      ∀ boundary →
      R370.AnalyticFamily sensitivity
        (λ background →
          R103.cmp116PhysicalMarkedHessian literal background
            (leftVariation boundary) (rightVariation boundary))

    sourceHessianUniformlyBounded :
      ∀ boundary →
      R370.UniformMagnitudeBound sensitivity
        (λ background →
          R103.cmp116PhysicalMarkedHessian literal background
            (leftVariation boundary) (rightVariation boundary))
        sourceMagnitudeBound

    sourceRadiusPositive :
      R370.PositiveRadiusMargin sensitivity sourceRadius

    leftSubstituted rightSubstituted :
      Boundary → Source.Background (R103.source literal)

    selectedSubstitutedBackgroundsShareNeighbourhood :
      ∀ boundary →
      R370.CommonNeighbourhood sensitivity
        (leftSubstituted boundary) (rightSubstituted boundary)

    selectedSubstitutionDistanceBelowSourceDistance :
      ∀ boundary →
      R370.parameterDistance sensitivity
        (leftSubstituted boundary) (rightSubstituted boundary)
      ≤ℝ sourceSubstitutionDistance boundary

open LiteralR103HessianSensitivityData public

literalR103HessianFamily :
  ∀ {literal} →
  (dataSet : LiteralR103HessianSensitivityData literal) →
  Boundary dataSet → Source.Background (R103.source literal) → ℝ
literalR103HessianFamily {literal} dataSet boundary background =
  R103.cmp116PhysicalMarkedHessian literal background
    (leftVariation dataSet boundary)
    (rightVariation dataSet boundary)

literalR103HessianDifference :
  ∀ {literal} →
  (dataSet : LiteralR103HessianSensitivityData literal) →
  Boundary dataSet → ℝ
literalR103HessianDifference dataSet boundary =
  R370.backgroundDistance (sensitivity dataSet)
    (literalR103HessianFamily dataSet boundary
      (leftSubstituted dataSet boundary))
    (literalR103HessianFamily dataSet boundary
      (rightSubstituted dataSet boundary))

asR372LiteralHessianSensitivity :
  ∀ {literal} →
  LiteralR103HessianSensitivityData literal →
  R372.CMP116DirectHessianSensitivityData
asR372LiteralHessianSensitivity {literal} dataSet = record
  { R372.CMP116DirectHessianSensitivityData.SubstitutedBackground =
      Source.Background (R103.source literal)
  ; R372.CMP116DirectHessianSensitivityData.HessianValue = ℝ
  ; R372.CMP116DirectHessianSensitivityData.Boundary = Boundary dataSet
  ; R372.CMP116DirectHessianSensitivityData.sensitivity = sensitivity dataSet
  ; R372.CMP116DirectHessianSensitivityData.hessianFamily =
      literalR103HessianFamily dataSet
  ; R372.CMP116DirectHessianSensitivityData.sourceMagnitudeBound =
      sourceMagnitudeBound dataSet
  ; R372.CMP116DirectHessianSensitivityData.sourceRadius = sourceRadius dataSet
  ; R372.CMP116DirectHessianSensitivityData.sourceSubstitutionDistance =
      sourceSubstitutionDistance dataSet
  ; R372.CMP116DirectHessianSensitivityData.sourceSubstitutionDistanceNonnegative =
      sourceSubstitutionDistanceNonnegative dataSet
  ; R372.CMP116DirectHessianSensitivityData.sourceHessianAnalytic =
      sourceHessianAnalytic dataSet
  ; R372.CMP116DirectHessianSensitivityData.sourceHessianUniformlyBounded =
      sourceHessianUniformlyBounded dataSet
  ; R372.CMP116DirectHessianSensitivityData.sourceRadiusPositive =
      sourceRadiusPositive dataSet
  ; R372.CMP116DirectHessianSensitivityData.leftSubstituted =
      leftSubstituted dataSet
  ; R372.CMP116DirectHessianSensitivityData.rightSubstituted =
      rightSubstituted dataSet
  ; R372.CMP116DirectHessianSensitivityData.selectedSubstitutedBackgroundsShareNeighbourhood =
      selectedSubstitutedBackgroundsShareNeighbourhood dataSet
  ; R372.CMP116DirectHessianSensitivityData.selectedSubstitutionDistanceBelowSourceDistance =
      selectedSubstitutionDistanceBelowSourceDistance dataSet
  ; R372.CMP116DirectHessianSensitivityData.sourceHessianDifference =
      literalR103HessianDifference dataSet
  ; R372.CMP116DirectHessianSensitivityData.sourceHessianDifferenceIsTargetDistance =
      λ _ → refl
  }

literalR103HessianFamilyIsSelectedR372Family :
  ∀ {literal}
    (dataSet : LiteralR103HessianSensitivityData literal)
    boundary background →
  R372.hessianFamily (asR372LiteralHessianSensitivity dataSet) boundary background
  ≡ R103.cmp116PhysicalMarkedHessian literal background
      (leftVariation dataSet boundary)
      (rightVariation dataSet boundary)
literalR103HessianFamilyIsSelectedR372Family dataSet boundary background = refl

literalR103DifferenceIsTargetDistance :
  ∀ {literal}
    (dataSet : LiteralR103HessianSensitivityData literal)
    boundary →
  R372.sourceHessianDifference (asR372LiteralHessianSensitivity dataSet) boundary
  ≡ R370.backgroundDistance (sensitivity dataSet)
      (literalR103HessianFamily dataSet boundary
        (leftSubstituted dataSet boundary))
      (literalR103HessianFamily dataSet boundary
        (rightSubstituted dataSet boundary))
literalR103DifferenceIsTargetDistance dataSet boundary = refl

------------------------------------------------------------------------
-- Pareto / authority boundary.
------------------------------------------------------------------------

round383LiteralHessianAdapterCompilerLevel : ProofLevel
round383LiteralHessianAdapterCompilerLevel = machineChecked

literalR103HessianFamilyChosenByConstruction : Bool
literalR103HessianFamilyChosenByConstruction = true

literalR103HessianFamilyChosenByConstructionIsTrue :
  literalR103HessianFamilyChosenByConstruction ≡ true
literalR103HessianFamilyChosenByConstructionIsTrue = refl

freeHessianDifferenceCoordinateRequiredAfterRound383 : Bool
freeHessianDifferenceCoordinateRequiredAfterRound383 = false

freeHessianDifferenceCoordinateRequiredAfterRound383IsFalse :
  freeHessianDifferenceCoordinateRequiredAfterRound383 ≡ false
freeHessianDifferenceCoordinateRequiredAfterRound383IsFalse = refl

selectedAnalyticCalibrationStillRequired : Bool
selectedAnalyticCalibrationStillRequired = true

selectedAnalyticCalibrationStillRequiredIsTrue :
  selectedAnalyticCalibrationStillRequired ≡ true
selectedAnalyticCalibrationStillRequiredIsTrue = refl

sourceCitationAlonePaysSelectedAnalyticCalibration : Bool
sourceCitationAlonePaysSelectedAnalyticCalibration = false

sourceCitationAlonePaysSelectedAnalyticCalibrationIsFalse :
  sourceCitationAlonePaysSelectedAnalyticCalibration ≡ false
sourceCitationAlonePaysSelectedAnalyticCalibrationIsFalse = refl

literalR103CarrierInstantiationLevel : ProofLevel
literalR103CarrierInstantiationLevel = R103.literalDifferentiatedCarrierInstantiationLevel

selectedR103HessianAnalyticCalibrationLevel : ProofLevel
selectedR103HessianAnalyticCalibrationLevel = conditional

clayPromotion : Bool
clayPromotion = false

clayPromotionIsFalse : clayPromotion ≡ false
clayPromotionIsFalse = refl
