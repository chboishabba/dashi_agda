module DASHI.Physics.YangMills.BalabanCMP116DirectHessianSensitivityRound372Exact where

------------------------------------------------------------------------
-- ROUND372 / H_local IS ANOTHER PARAMETRIC-SENSITIVITY CONSUMER
--
-- R352 asks for the literal CMP116 LOCAL twice-varied activity stability
--
--   Hdiff <= L_source * d_sub.
--
-- It does not ask for the full physical-background Hessian chain rule.  CMP116
-- Sect. 1 already places the localized activity on one common complex analytic
-- domain and explicitly differentiates a finite number of times by Cauchy
-- formula while retaining uniform bounds/localization.  Therefore the shortest
-- producer for H_local is structurally the same as R370's producer for
-- H_subScale:
--
--   analytic Hessian family on one common neighbourhood
--   + uniform magnitude bound
--   + positive radius margin
--   + selected parameter-distance upper
--   -> Cauchy parametric sensitivity
--   -> Hdiff <= L_source * d_sub.
--
-- This module REUSES R370.CauchyParametricSensitivityAuthority.  It does not
-- create a second calculus interface and does not require a separately named
-- third-derivative theorem.
--
-- Fail-closed boundary: CMP116 source authority for finite differentiated
-- analytic activities does not by citation identify the selected R352 Hessian
-- family, norm/distance, common neighbourhood, or quantitative radius/magnitude
-- constants.  Those are explicit application fields below.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

open import DASHI.Foundations.RealAnalysisAxioms using
  (ℝ; 0ℝ; _≤ℝ_)
open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Physics.YangMills.BalabanCMP116DirectParametricSensitivityRound370Exact as R370
import DASHI.Physics.YangMills.BalabanCMP116DifferentiatedLocalizationSourceExact as Source
import DASHI.Physics.YangMills.BalabanSelectedHessianStabilitySourceRound352Exact as R352

------------------------------------------------------------------------
-- Selected source application.
------------------------------------------------------------------------

record CMP116DirectHessianSensitivityData : Set₁ where
  field
    SubstitutedBackground HessianValue Boundary : Set

    sensitivity :
      R370.CauchyParametricSensitivityAuthority
        SubstitutedBackground HessianValue

    -- The local twice-varied activity, viewed as a function of the substituted
    -- background on the SAME source analytic carrier.
    hessianFamily : Boundary → SubstitutedBackground → HessianValue

    sourceMagnitudeBound sourceRadius sourceSubstitutionDistance : ℝ
    sourceSubstitutionDistanceNonnegative :
      0ℝ ≤ℝ sourceSubstitutionDistance

    sourceHessianAnalytic :
      ∀ boundary →
      R370.AnalyticFamily sensitivity (hessianFamily boundary)

    sourceHessianUniformlyBounded :
      ∀ boundary →
      R370.UniformMagnitudeBound sensitivity
        (hessianFamily boundary) sourceMagnitudeBound

    sourceRadiusPositive :
      R370.PositiveRadiusMargin sensitivity sourceRadius

    leftSubstituted rightSubstituted : Boundary → SubstitutedBackground

    selectedSubstitutedBackgroundsShareNeighbourhood :
      ∀ boundary →
      R370.CommonNeighbourhood sensitivity
        (leftSubstituted boundary) (rightSubstituted boundary)

    selectedSubstitutionDistanceBelowSourceDistance :
      ∀ boundary →
      R370.parameterDistance sensitivity
        (leftSubstituted boundary) (rightSubstituted boundary)
      ≤ℝ sourceSubstitutionDistance

    -- Same-object scalarization consumed by R352.  The source Hessian
    -- difference is exactly the target-space distance between the two values of
    -- the selected local Hessian family.
    sourceHessianDifference : Boundary → ℝ
    sourceHessianDifferenceIsTargetDistance :
      ∀ boundary →
      sourceHessianDifference boundary ≡
      R370.backgroundDistance sensitivity
        (hessianFamily boundary (leftSubstituted boundary))
        (hessianFamily boundary (rightSubstituted boundary))

open CMP116DirectHessianSensitivityData public

sourceHessianLipschitz : CMP116DirectHessianSensitivityData → ℝ
sourceHessianLipschitz dataSet =
  R370.lipschitzConstant (sensitivity dataSet)
    (sourceMagnitudeBound dataSet) (sourceRadius dataSet)

sourceHessianStableFromCauchy :
  (dataSet : CMP116DirectHessianSensitivityData) →
  ∀ boundary →
  sourceHessianDifference dataSet boundary
    ≤ℝ
  sourceHessianLipschitz dataSet *
    sourceSubstitutionDistance dataSet
sourceHessianStableFromCauchy dataSet boundary
  rewrite sourceHessianDifferenceIsTargetDistance dataSet boundary =
  R370.cauchySensitivityWithDistanceUpper (sensitivity dataSet)
    (hessianFamily dataSet boundary)
    (sourceMagnitudeBound dataSet)
    (sourceRadius dataSet)
    (leftSubstituted dataSet boundary)
    (rightSubstituted dataSet boundary)
    (sourceSubstitutionDistance dataSet)
    (sourceHessianAnalytic dataSet boundary)
    (sourceHessianUniformlyBounded dataSet boundary)
    (sourceRadiusPositive dataSet)
    (selectedSubstitutedBackgroundsShareNeighbourhood dataSet boundary)
    (selectedSubstitutionDistanceBelowSourceDistance dataSet boundary)

round372ToR352Source :
  (dataSet : CMP116DirectHessianSensitivityData) →
  R352.CMP116LocalHessianStabilitySource (Boundary dataSet)
round372ToR352Source dataSet = record
  { R352.sourceHessianDifference = sourceHessianDifference dataSet
  ; R352.sourceLipschitz = sourceHessianLipschitz dataSet
  ; R352.sourceSubstitutionDistance =
      λ _ → sourceSubstitutionDistance dataSet
  ; R352.sourceHessianStable = sourceHessianStableFromCauchy dataSet
  }

------------------------------------------------------------------------
-- Pareto / authority boundary.
------------------------------------------------------------------------

standardCauchyHessianSensitivityLevel : ProofLevel
standardCauchyHessianSensitivityLevel = R370.standardCauchyParametricSensitivityLevel

cmp116FiniteDifferentiatedAnalyticityLevel : ProofLevel
cmp116FiniteDifferentiatedAnalyticityLevel =
  Source.cmp116DifferentiatedActivityLocalizationLevel

cmp116FiniteDerivativeCauchyLevel : ProofLevel
cmp116FiniteDerivativeCauchyLevel =
  Source.finitePolydiscCauchyDerivativePreservesExternalMajorantLevel

literalCMP116SelectedHessianFamilyAttachmentLevel : ProofLevel
literalCMP116SelectedHessianFamilyAttachmentLevel = conditional

literalCMP116HessianCommonNeighbourhoodLevel : ProofLevel
literalCMP116HessianCommonNeighbourhoodLevel = conditional

literalCMP116HessianRadiusMagnitudeCalibrationLevel : ProofLevel
literalCMP116HessianRadiusMagnitudeCalibrationLevel = conditional

literalCMP116HessianDistanceScalarizationLevel : ProofLevel
literalCMP116HessianDistanceScalarizationLevel = conditional

round372ToR352CompilerLevel : ProofLevel
round372ToR352CompilerLevel = machineChecked

hLocalPrimitiveAfterRound372 : Bool
hLocalPrimitiveAfterRound372 = false

hLocalPrimitiveAfterRound372IsFalse :
  hLocalPrimitiveAfterRound372 ≡ false
hLocalPrimitiveAfterRound372IsFalse = refl

separateThirdDerivativeTheoremMandatoryAfterRound372 : Bool
separateThirdDerivativeTheoremMandatoryAfterRound372 = false

separateThirdDerivativeTheoremMandatoryAfterRound372IsFalse :
  separateThirdDerivativeTheoremMandatoryAfterRound372 ≡ false
separateThirdDerivativeTheoremMandatoryAfterRound372IsFalse = refl

fullPhysicalSubstitutionChainRuleMandatoryForR352 : Bool
fullPhysicalSubstitutionChainRuleMandatoryForR352 = false

fullPhysicalSubstitutionChainRuleMandatoryForR352IsFalse :
  fullPhysicalSubstitutionChainRuleMandatoryForR352 ≡ false
fullPhysicalSubstitutionChainRuleMandatoryForR352IsFalse = refl

sourceAnalyticityAutomaticallyPaysSelectedHessianFamily : Bool
sourceAnalyticityAutomaticallyPaysSelectedHessianFamily = false

sourceAnalyticityAutomaticallyPaysSelectedHessianFamilyIsFalse :
  sourceAnalyticityAutomaticallyPaysSelectedHessianFamily ≡ false
sourceAnalyticityAutomaticallyPaysSelectedHessianFamilyIsFalse = refl

record Round372Boundary : Set where
  constructor round372-boundary
  field
    cauchySensitivityReusedForHLocal : Bool
    cauchySensitivityReusedForHLocalIsTrue :
      cauchySensitivityReusedForHLocal ≡ true

    sameObjectHessianFamilyStillRequired : Bool
    sameObjectHessianFamilyStillRequiredIsTrue :
      sameObjectHessianFamilyStillRequired ≡ true

    commonRadiusAndMagnitudeStillQuantitative : Bool
    commonRadiusAndMagnitudeStillQuantitativeIsTrue :
      commonRadiusAndMagnitudeStillQuantitative ≡ true

canonicalRound372Boundary : Round372Boundary
canonicalRound372Boundary =
  round372-boundary true refl true refl true refl

round372FrontierRefinementLevel : ProofLevel
round372FrontierRefinementLevel = machineChecked

clayPromotion : Bool
clayPromotion = false

clayPromotionIsFalse : clayPromotion ≡ false
clayPromotionIsFalse = refl
