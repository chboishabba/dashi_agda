module DASHI.Physics.YangMills.BalabanCMP116HessianBidiBridgeRound375Exact where

------------------------------------------------------------------------
-- ROUND375 / BIDI: DIRECT HESSIAN SENSITIVITY -> MARKED COEFFICIENT
--
-- R372/R373 recut H_local as direct Cauchy parametric sensitivity on the
-- selected local Hessian family.  Much older repository machinery already
-- proves the reverse-facing Cauchy lift needed by the marked route:
--
--   pointwise boundary Hessian difference <= L * d_sub(s)
--   + d_sub(s) <= markedInput
--   ----------------------------------------------------
--   decoupled Hessian coefficient difference <= L * markedInput.
--
-- This owner performs that missing BIDI splice on the SAME
-- `DecoupledActivityHessianData` carried by R373.  It does not identify the
-- selected physical decoupled object by citation and it does not manufacture
-- the marked-input bound.  Those remain explicit same-object/application
-- payments.
--
-- Consequence: the R353 marked-walk route and its standalone
-- `M_Hessian <= L * d_sub` scale comparison remain valid producers, but they
-- are not architecturally mandatory when the direct R372/R373 source theorem
-- and the selected marked-input upper are available on the same carrier.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

open import DASHI.Foundations.RealAnalysisAxioms using
  (ℝ; 0ℝ; _*ℝ_; _≤ℝ_)
open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Foundations.FinitePolydiscCauchyAxioms as Cauchy

import DASHI.Physics.YangMills.BalabanDecoupledActivityHessian as Decoupled
import DASHI.Physics.YangMills.BalabanCMP116JointParametricSensitivityRound373Exact as R373

------------------------------------------------------------------------
-- Least-privilege BIDI application data.
------------------------------------------------------------------------

record CMP116HessianBidiBridgeData : Set₁ where
  field
    joint : R373.JointBoundaryHessianPaymentData

    markedInput : ℝ

    selectedLipschitzNonnegative :
      0ℝ ≤ℝ R373.selectedLipschitz joint

    selectedBoundaryDistanceNonnegative :
      ∀ s → 0ℝ ≤ℝ R373.selectedBoundarySubstitutionDistance joint s

    markedInputNonnegative : 0ℝ ≤ℝ markedInput

    -- This is the only new quantitative comparison needed by the bridge:
    -- the already-selected substitution distance sits below the marked source
    -- input used by the coefficient/marked route.
    selectedBoundaryDistanceBelowMarkedInput :
      ∀ s →
      R373.selectedBoundarySubstitutionDistance joint s ≤ℝ markedInput

open CMP116HessianBidiBridgeData public

------------------------------------------------------------------------
-- Existing theorem reuse.
------------------------------------------------------------------------

selectedCoefficientDifferenceBound :
  (dataSet : CMP116HessianBidiBridgeData) →
  Cauchy.normValue
    (Decoupled.cauchy (R373.decoupled (joint dataSet)))
    (Cauchy._-Value_
      (Decoupled.cauchy (R373.decoupled (joint dataSet)))
      (Decoupled.decoupledHessianCoefficient
        (R373.decoupled (joint dataSet))
        (R373.leftDomain (joint dataSet))
        (R373.component (joint dataSet))
        (R373.leftVariation (joint dataSet))
        (R373.rightVariation (joint dataSet)))
      (Decoupled.decoupledHessianCoefficient
        (R373.decoupled (joint dataSet))
        (R373.rightDomain (joint dataSet))
        (R373.component (joint dataSet))
        (R373.leftVariation (joint dataSet))
        (R373.rightVariation (joint dataSet))))
  ≤ℝ
  R373.selectedLipschitz (joint dataSet) *ℝ markedInput dataSet
selectedCoefficientDifferenceBound dataSet =
  Decoupled.markedSubstitutionStabilityLiftsToCoefficient
    (R373.decoupled (joint dataSet))
    (R373.leftDomain (joint dataSet))
    (R373.rightDomain (joint dataSet))
    (R373.component (joint dataSet))
    (R373.leftVariation (joint dataSet))
    (R373.rightVariation (joint dataSet))
    (R373.selectedLipschitz (joint dataSet))
    (markedInput dataSet)
    (R373.selectedBoundarySubstitutionDistance (joint dataSet))
    (selectedLipschitzNonnegative dataSet)
    (selectedBoundaryDistanceNonnegative dataSet)
    (markedInputNonnegative dataSet)
    (R373.boundaryHessianStableFromR372 (joint dataSet))
    (selectedBoundaryDistanceBelowMarkedInput dataSet)

------------------------------------------------------------------------
-- Pareto / authority boundary.
------------------------------------------------------------------------

round375BidiCompilerLevel : ProofLevel
round375BidiCompilerLevel = machineChecked

literalSelectedDecoupledHessianSameObjectLevel : ProofLevel
literalSelectedDecoupledHessianSameObjectLevel = conditional

literalSelectedDistanceToMarkedInputLevel : ProofLevel
literalSelectedDistanceToMarkedInputLevel = conditional

directHessianSensitivityFeedsMarkedCoefficient : Bool
directHessianSensitivityFeedsMarkedCoefficient = true

directHessianSensitivityFeedsMarkedCoefficientIsTrue :
  directHessianSensitivityFeedsMarkedCoefficient ≡ true
directHessianSensitivityFeedsMarkedCoefficientIsTrue = refl

separateMarkedMajorantHScaleMandatoryAfterRound375 : Bool
separateMarkedMajorantHScaleMandatoryAfterRound375 = false

separateMarkedMajorantHScaleMandatoryAfterRound375IsFalse :
  separateMarkedMajorantHScaleMandatoryAfterRound375 ≡ false
separateMarkedMajorantHScaleMandatoryAfterRound375IsFalse = refl

sameObjectDecoupledHessianAttachmentStillRequired : Bool
sameObjectDecoupledHessianAttachmentStillRequired = true

sameObjectDecoupledHessianAttachmentStillRequiredIsTrue :
  sameObjectDecoupledHessianAttachmentStillRequired ≡ true
sameObjectDecoupledHessianAttachmentStillRequiredIsTrue = refl

record Round375Boundary : Set where
  constructor round375-boundary
  field
    directRouteReusesMarkedCoefficientLift : Bool
    directRouteReusesMarkedCoefficientLiftIsTrue :
      directRouteReusesMarkedCoefficientLift ≡ true

    newCauchyOrMeanValueTheoremRequired : Bool
    newCauchyOrMeanValueTheoremRequiredIsFalse :
      newCauchyOrMeanValueTheoremRequired ≡ false

    physicalSameObjectAndMarkedInputAttachmentsRemain : Bool
    physicalSameObjectAndMarkedInputAttachmentsRemainIsTrue :
      physicalSameObjectAndMarkedInputAttachmentsRemain ≡ true

canonicalRound375Boundary : Round375Boundary
canonicalRound375Boundary =
  round375-boundary true refl false refl true refl

round375FrontierRefinementLevel : ProofLevel
round375FrontierRefinementLevel = machineChecked

clayPromotion : Bool
clayPromotion = false

clayPromotionIsFalse : clayPromotion ≡ false
clayPromotionIsFalse = refl
