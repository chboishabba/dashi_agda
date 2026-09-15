module DASHI.Physics.YangMills.BalabanCMP116SelectedMarkedBoundaryCutRound347Exact where

------------------------------------------------------------------------
-- ROUND347 / SELECTED MARKED-BOUNDARY CUT BELOW R346 L_marked
--
-- R346 correctly exposes the literal selected localization
--
--   |D^2_{J_L,J_R} log Z| <= markedAnalyticShell(hessianMark)
--
-- as a proof-bearing physical/source application.  This owner descends that
-- leaf one level further without manufacturing the missing estimate.
--
-- Existing repo theorem:
--   BalabanDecoupledActivityHessian proves the generic finite-polydisc/Cauchy
--   lift from a pointwise marked boundary comparison to the corresponding
--   Hessian coefficient estimate.  Its source-shaped short route also makes
--   explicit that domain dependence may be paid by controlling the nonlinear
--   substituted-background difference and then applying Hessian stability.
--
-- Therefore the Cauchy coefficient extraction itself is compiler-owned.  The
-- first source-specific analytic/application coordinate is the pointwise
-- selected marked-boundary/substitution comparison on the literal selected J
-- pair, together with the same-object attachment of those J directions to the
-- source physical coordinates.  R346's support-distance = Euclidean-time field
-- remains a separate physical semantics coordinate.
--
-- This file deliberately does NOT claim that either selected payment is
-- inhabited, and it does not derive R346.literalSelectedDifferentiatedLocalization.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanDecoupledActivityHessian as Hess
import DASHI.Physics.YangMills.BalabanCMP116DifferentiatedLocalizationSourceExact as Source
import DASHI.Physics.YangMills.BalabanCMP116SharedMarkedAmplitudeDirectRound346Exact as R346

------------------------------------------------------------------------
-- Canonical current acquisition cut.
------------------------------------------------------------------------

record SelectedMarkedBoundaryAcquisition : Set₁ where
  constructor selected-marked-boundary-acquisition
  field
    -- Literal CMP116 boundary/substitution comparison on the selected pair.
    SelectedPointwiseBoundaryComparison : Set
    selectedPointwiseBoundaryComparison : SelectedPointwiseBoundaryComparison

    -- Same-object attachment of R318's selected J(F),J(G) to the source
    -- boundary-coordinate directions consumed by the previous field.
    SelectedJPhysicalCoordinateAttachment : Set
    selectedJPhysicalCoordinateAttachment : SelectedJPhysicalCoordinateAttachment

open SelectedMarkedBoundaryAcquisition public

------------------------------------------------------------------------
-- Existing compiler/status reuse.
------------------------------------------------------------------------

genericMarkedBoundaryToHessianLiftLevel : ProofLevel
genericMarkedBoundaryToHessianLiftLevel =
  Source.markedBoundaryToHessianCauchyLiftLevel

selectedBoundarySubstitutionComparisonLevel : ProofLevel
selectedBoundarySubstitutionComparisonLevel = conditional

selectedJPhysicalCoordinateAttachmentLevel : ProofLevel
selectedJPhysicalCoordinateAttachmentLevel = conditional

selectedDistanceTimeMeaningLevel : ProofLevel
selectedDistanceTimeMeaningLevel = R346.round346SelectedPhysicalDistanceMeaningLevel

------------------------------------------------------------------------
-- Fail-closed route classification.
------------------------------------------------------------------------

record Round347Boundary : Set where
  constructor round347-boundary
  field
    finitePolydiscCauchyLiftIsNewYMAnalysis : Bool
    finitePolydiscCauchyLiftIsNewYMAnalysisIsFalse :
      finitePolydiscCauchyLiftIsNewYMAnalysis ≡ false

    sourceSpecificBoundaryComparisonStillProofBearing : Bool
    sourceSpecificBoundaryComparisonStillProofBearingIsTrue :
      sourceSpecificBoundaryComparisonStillProofBearing ≡ true

    selectedJCoordinateAttachmentStillProofBearing : Bool
    selectedJCoordinateAttachmentStillProofBearingIsTrue :
      selectedJCoordinateAttachmentStillProofBearing ≡ true

    selectedDistanceTimeMeaningStillProofBearing : Bool
    selectedDistanceTimeMeaningStillProofBearingIsTrue :
      selectedDistanceTimeMeaningStillProofBearing ≡ true

    abstractSourceEnvelopeCalibrationMandatory : Bool
    abstractSourceEnvelopeCalibrationMandatoryIsFalse :
      abstractSourceEnvelopeCalibrationMandatory ≡ false

    hessianConstantUpperOneMandatory : Bool
    hessianConstantUpperOneMandatoryIsFalse :
      hessianConstantUpperOneMandatory ≡ false

    literalR346LocalizationAlreadyPaid : Bool
    literalR346LocalizationAlreadyPaidIsFalse :
      literalR346LocalizationAlreadyPaid ≡ false

canonicalRound347Boundary : Round347Boundary
canonicalRound347Boundary =
  round347-boundary
    false refl
    true refl
    true refl
    true refl
    false refl
    false refl
    false refl

-- The generic compiler exists in-repo, but the selected source-specific
-- comparison and coordinate attachment remain theorem-bearing.  This owner is
-- therefore a frontier refinement, not a Clay/YM completion theorem.
round347FrontierRefinementLevel : ProofLevel
round347FrontierRefinementLevel = machineChecked

clayPromotion : Bool
clayPromotion = false

clayPromotionIsFalse : clayPromotion ≡ false
clayPromotionIsFalse = refl
