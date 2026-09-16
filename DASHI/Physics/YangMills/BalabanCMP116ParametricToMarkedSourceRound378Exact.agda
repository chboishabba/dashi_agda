{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanCMP116ParametricToMarkedSourceRound378Exact where

------------------------------------------------------------------------
-- ROUND378 / R370 PARAMETRIC DISPLACEMENT -> R351 H_sub SOURCE OBJECT
--
-- CMP116 Sect. 1 constructs the substituted background as an analytic function
-- of the decoupling parameters s(Y0), uniformly bounded on one common complex
-- neighbourhood.  R370 already compiles exactly that theorem shape into
--
--   boundary substitution distance
--     <= source parametric Lipschitz * source parameter distance.
--
-- R351 had retained the stronger source-facing primitive
--
--   d_sub^src <= M_marked^src.
--
-- The latter is not independent once the R370 family is the same source family.
-- The only additional scalar payment is the calibration
--
--   source parametric Lipschitz * source parameter distance <= M_marked^src.
--
-- This file performs only that ordered transport and constructs the exact R351
-- source ABI.  It does not identify the selected CMP116 family, manufacture the
-- common neighbourhood/radius/magnitude data, or prove the parameter-to-mark
-- calibration.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

open import DASHI.Foundations.RealAnalysisAxioms using (ℝ; 0ℝ; _≤ℝ_; ≤ℝ-trans)
open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Foundations.FinitePolydiscCauchyAxioms as Cauchy

import DASHI.Physics.YangMills.BalabanDecoupledActivityHessian as Decoupled
import DASHI.Physics.YangMills.BalabanCMP116DirectParametricSensitivityRound370Exact as R370
import DASHI.Physics.YangMills.BalabanSelectedSubstitutionMarkedSourceRound351Exact as R351

------------------------------------------------------------------------
-- Same boundary carrier used by the literal R370 selected fixed-point family.
------------------------------------------------------------------------

BoundaryPoint : R370.CMP116DirectParametricSensitivityData → Set
BoundaryPoint dataSet =
  Cauchy.BoundaryAssignment
    (Decoupled.cauchy (R370.decoupled dataSet))
    (Decoupled.componentIndices
      (R370.decoupled dataSet)
      (R370.component dataSet))

record CMP116ParametricToMarkedSourceData : Set₁ where
  field
    parametric : R370.CMP116DirectParametricSensitivityData

    sourceMarkedInput : ℝ
    sourceMarkedInputNonnegative : 0ℝ ≤ℝ sourceMarkedInput

    -- The only new source/application payment introduced by R378.
    -- R370 already proves d_sub <= sourceSubstitutionDistance.
    parametricScaleBelowMarkedInput :
      R370.sourceSubstitutionDistance parametric ≤ℝ sourceMarkedInput

open CMP116ParametricToMarkedSourceData public

asR351SubstitutionMarkedSource :
  (dataSet : CMP116ParametricToMarkedSourceData) →
  R351.CMP116SubstitutionMarkedSource
    (BoundaryPoint (parametric dataSet))
asR351SubstitutionMarkedSource dataSet = record
  { R351.CMP116SubstitutionMarkedSource.sourceSubstitutionDistance =
      R370.boundarySubstitutionDistance (parametric dataSet)
  ; R351.CMP116SubstitutionMarkedSource.sourceMarkedInput =
      sourceMarkedInput dataSet
  ; R351.CMP116SubstitutionMarkedSource.sourceDistanceNonnegative =
      R370.boundarySubstitutionDistanceNonnegativeFromParametric
        (parametric dataSet)
  ; R351.CMP116SubstitutionMarkedSource.sourceMarkedInputNonnegative =
      sourceMarkedInputNonnegative dataSet
  ; R351.CMP116SubstitutionMarkedSource.sourceSubstitutionMarked =
      λ point →
        ≤ℝ-trans
          (R370.boundarySubstitutionBelowSourceDistanceFromParametric
            (parametric dataSet) point)
          (parametricScaleBelowMarkedInput dataSet)
  }

round378SourceSubstitutionMarked :
  (dataSet : CMP116ParametricToMarkedSourceData) →
  ∀ point →
  R351.sourceSubstitutionDistance (asR351SubstitutionMarkedSource dataSet) point
    ≤ℝ
  R351.sourceMarkedInput (asR351SubstitutionMarkedSource dataSet)
round378SourceSubstitutionMarked dataSet point =
  R351.sourceSubstitutionMarked
    (asR351SubstitutionMarkedSource dataSet) point

------------------------------------------------------------------------
-- Pareto / authority boundary.
------------------------------------------------------------------------

round378ParametricToR351CompilerLevel : ProofLevel
round378ParametricToR351CompilerLevel = machineChecked

cmp116ParametricSensitivitySourceLevel : ProofLevel
cmp116ParametricSensitivitySourceLevel =
  R370.cmp116FixedPointAnalyticInDecouplingParametersLevel

literalParametricFamilyAttachmentLevel : ProofLevel
literalParametricFamilyAttachmentLevel =
  R370.literalCMP116ParametricFamilySameObjectAttachmentLevel

literalCommonParameterNeighbourhoodLevel : ProofLevel
literalCommonParameterNeighbourhoodLevel =
  R370.literalCMP116CommonParameterNeighbourhoodLevel

literalParameterDistanceCalibrationLevel : ProofLevel
literalParameterDistanceCalibrationLevel =
  R370.literalCMP116ParameterDistanceCalibrationLevel

literalParametricScaleToMarkedInputCalibrationLevel : ProofLevel
literalParametricScaleToMarkedInputCalibrationLevel = conditional

r370ParametricSensitivityFeedsR351 : Bool
r370ParametricSensitivityFeedsR351 = true

r370ParametricSensitivityFeedsR351IsTrue :
  r370ParametricSensitivityFeedsR351 ≡ true
r370ParametricSensitivityFeedsR351IsTrue = refl

r351StandaloneSourceDisplacementPrimitiveAfterRound378 : Bool
r351StandaloneSourceDisplacementPrimitiveAfterRound378 = false

r351StandaloneSourceDisplacementPrimitiveAfterRound378IsFalse :
  r351StandaloneSourceDisplacementPrimitiveAfterRound378 ≡ false
r351StandaloneSourceDisplacementPrimitiveAfterRound378IsFalse = refl

parametricScaleToMarkedInputCalibrationStillRequired : Bool
parametricScaleToMarkedInputCalibrationStillRequired = true

parametricScaleToMarkedInputCalibrationStillRequiredIsTrue :
  parametricScaleToMarkedInputCalibrationStillRequired ≡ true
parametricScaleToMarkedInputCalibrationStillRequiredIsTrue = refl

freshHessianAnalysisRequiredAfterRound378 : Bool
freshHessianAnalysisRequiredAfterRound378 = false

freshHessianAnalysisRequiredAfterRound378IsFalse :
  freshHessianAnalysisRequiredAfterRound378 ≡ false
freshHessianAnalysisRequiredAfterRound378IsFalse = refl

record Round378Boundary : Set where
  constructor round378-boundary
  field
    directParametricDisplacementReused : Bool
    directParametricDisplacementReusedIsTrue :
      directParametricDisplacementReused ≡ true

    standaloneHSubSourceTheoremStillPrimitive : Bool
    standaloneHSubSourceTheoremStillPrimitiveIsFalse :
      standaloneHSubSourceTheoremStillPrimitive ≡ false

    oneScalarParameterToMarkCalibrationRemains : Bool
    oneScalarParameterToMarkCalibrationRemainsIsTrue :
      oneScalarParameterToMarkCalibrationRemains ≡ true

canonicalRound378Boundary : Round378Boundary
canonicalRound378Boundary =
  round378-boundary true refl false refl true refl

round378FrontierRefinementLevel : ProofLevel
round378FrontierRefinementLevel = machineChecked

clayPromotion : Bool
clayPromotion = false

clayPromotionIsFalse : clayPromotion ≡ false
clayPromotionIsFalse = refl
