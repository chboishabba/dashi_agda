{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanCMP116CanonicalR370R373BoundaryRound381Exact where

------------------------------------------------------------------------
-- ROUND381 / ONE SELECTED BOUNDARY DISTANCE, NOT AN R373<->R370 WELD
--
-- R380 still accepted a proof-bearing equality
--
--   R373.selectedBoundarySubstitutionDistance joint s
--     = R370.boundarySubstitutionDistance parametric (iota s)
--
-- as a primitive same-object attachment.
--
-- On the preferred direct route that is avoidable representation debt.  The
-- R373 joint record does not require an independently meaningful selected
-- distance: it only needs the distance consumed by the R372 Hessian payment.
-- Therefore choose the R373 boundary carrier to BE the R370 boundary carrier
-- and choose its selected distance to BE R370.boundarySubstitutionDistance.
--
-- The historical R380 equality and boundary map then become refl.  The real
-- same-object obligations are pushed to the source-facing Hessian coordinates:
--
--   * R372 Hessian scalar = the literal boundary Hessian scalar;
--   * R372 Lipschitz coordinate = R370 selected/source Lipschitz coordinate;
--   * R372 substitution distance = the SAME R370 boundary fixed-point distance.
--
-- This owner does not prove any of those physical/source identifications.  It
-- only removes a duplicated selected-distance coordinate between two compilers.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import DASHI.Foundations.RealAnalysisAxioms using (0ℝ; _≤ℝ_)
open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Physics.YangMills.BalabanCMP116DirectParametricSensitivityRound370Exact as R370
import DASHI.Physics.YangMills.BalabanCMP116DirectHessianSensitivityRound372Exact as R372
import DASHI.Physics.YangMills.BalabanCMP116JointParametricSensitivityRound373Exact as R373
import DASHI.Physics.YangMills.BalabanCMP116ParametricDistanceUpperHessianRound380Exact as R380

record CanonicalR370R373BoundaryData : Set₁ where
  field
    parametric : R370.CMP116DirectParametricSensitivityData
    hessian : R372.CMP116DirectHessianSensitivityData

    -- The Hessian source is read on the exact same selected boundary index as
    -- the fixed-point sensitivity source.
    boundaryToHessianBoundary :
      R380.R370Boundary parametric → R372.Boundary hessian

    hessianDifferenceIsBoundaryNorm :
      ∀ s →
      R372.sourceHessianDifference hessian
        (boundaryToHessianBoundary s)
      ≡
      R373.boundaryNormDifference
        (R370.decoupled parametric)
        (R370.leftDomain parametric)
        (R370.rightDomain parametric)
        (R370.component parametric)
        (R370.leftVariation parametric)
        (R370.rightVariation parametric)
        s

    hessianLipschitzIsParametricLipschitz :
      R372.sourceHessianLipschitz hessian
      ≡ R370.sourceLipschitz parametric

    hessianDistanceIsParametricBoundaryDistance :
      ∀ s →
      R372.sourceSubstitutionDistance hessian
        (boundaryToHessianBoundary s)
      ≡ R370.boundarySubstitutionDistance parametric s

open CanonicalR370R373BoundaryData public

canonicalJoint :
  CanonicalR370R373BoundaryData →
  R373.JointBoundaryHessianPaymentData
canonicalJoint dataSet = record
  { R373.decoupled = R370.decoupled (parametric dataSet)
  ; R373.leftDomain = R370.leftDomain (parametric dataSet)
  ; R373.rightDomain = R370.rightDomain (parametric dataSet)
  ; R373.component = R370.component (parametric dataSet)
  ; R373.leftVariation = R370.leftVariation (parametric dataSet)
  ; R373.rightVariation = R370.rightVariation (parametric dataSet)
  ; R373.selectedLipschitz = R370.sourceLipschitz (parametric dataSet)
  ; R373.selectedBoundarySubstitutionDistance =
      R370.boundarySubstitutionDistance (parametric dataSet)
  ; R373.hessian = hessian dataSet
  ; R373.boundaryToHessianBoundary = boundaryToHessianBoundary dataSet
  ; R373.hessianDifferenceIsBoundaryNorm =
      hessianDifferenceIsBoundaryNorm dataSet
  ; R373.hessianLipschitzIsSelectedLipschitz =
      hessianLipschitzIsParametricLipschitz dataSet
  ; R373.hessianDistanceIsSelectedBoundaryDistance =
      hessianDistanceIsParametricBoundaryDistance dataSet
  }

canonicalRound380 :
  (dataSet : CanonicalR370R373BoundaryData) →
  (selectedLipschitzNonnegative :
    0ℝ ≤ℝ R370.sourceLipschitz (parametric dataSet)) →
  R380.CMP116ParametricDistanceUpperHessianData
canonicalRound380 dataSet selectedLipschitzNonnegative = record
  { R380.joint = canonicalJoint dataSet
  ; R380.parametric = parametric dataSet
  ; R380.jointBoundaryToParametricBoundary = λ s → s
  ; R380.selectedDistanceIsParametricBoundaryDistance = λ s → refl
  ; R380.selectedLipschitzNonnegative = selectedLipschitzNonnegative
  }

selectedDistanceIsLiterallyR370BoundaryDistance :
  (dataSet : CanonicalR370R373BoundaryData) →
  ∀ s →
  R373.selectedBoundarySubstitutionDistance (canonicalJoint dataSet) s
  ≡ R370.boundarySubstitutionDistance (parametric dataSet) s
selectedDistanceIsLiterallyR370BoundaryDistance dataSet s = refl

r380BoundaryMapIsIdentity :
  (dataSet : CanonicalR370R373BoundaryData) →
  (selectedLipschitzNonnegative :
    0ℝ ≤ℝ R370.sourceLipschitz (parametric dataSet)) →
  ∀ s →
  R380.jointBoundaryToParametricBoundary
    (canonicalRound380 dataSet selectedLipschitzNonnegative) s
  ≡ s
r380BoundaryMapIsIdentity dataSet selectedLipschitzNonnegative s = refl

------------------------------------------------------------------------
-- Pareto / authority boundary.
------------------------------------------------------------------------

round381CanonicalBoundaryCompilerLevel : ProofLevel
round381CanonicalBoundaryCompilerLevel = machineChecked

r373ToR370SelectedDistanceEqualityPrimitiveAfterRound381 : Bool
r373ToR370SelectedDistanceEqualityPrimitiveAfterRound381 = false

r373ToR370SelectedDistanceEqualityPrimitiveAfterRound381IsFalse :
  r373ToR370SelectedDistanceEqualityPrimitiveAfterRound381 ≡ false
r373ToR370SelectedDistanceEqualityPrimitiveAfterRound381IsFalse = refl

r373ToR370BoundaryMapPrimitiveAfterRound381 : Bool
r373ToR370BoundaryMapPrimitiveAfterRound381 = false

r373ToR370BoundaryMapPrimitiveAfterRound381IsFalse :
  r373ToR370BoundaryMapPrimitiveAfterRound381 ≡ false
r373ToR370BoundaryMapPrimitiveAfterRound381IsFalse = refl

literalHessianScalarizationStillRequired : Bool
literalHessianScalarizationStillRequired = true

literalHessianScalarizationStillRequiredIsTrue :
  literalHessianScalarizationStillRequired ≡ true
literalHessianScalarizationStillRequiredIsTrue = refl

hessianToFixedPointDistanceSameObjectStillRequired : Bool
hessianToFixedPointDistanceSameObjectStillRequired = true

hessianToFixedPointDistanceSameObjectStillRequiredIsTrue :
  hessianToFixedPointDistanceSameObjectStillRequired ≡ true
hessianToFixedPointDistanceSameObjectStillRequiredIsTrue = refl

record Round381Boundary : Set where
  constructor round381-boundary
  field
    oneSelectedBoundaryCarrierFeedsR370AndR373 : Bool
    oneSelectedBoundaryCarrierFeedsR370AndR373IsTrue :
      oneSelectedBoundaryCarrierFeedsR370AndR373 ≡ true

    selectedDistanceWeldReducedToRefl : Bool
    selectedDistanceWeldReducedToReflIsTrue :
      selectedDistanceWeldReducedToRefl ≡ true

    sourceFacingHessianAttachmentsRemainProofBearing : Bool
    sourceFacingHessianAttachmentsRemainProofBearingIsTrue :
      sourceFacingHessianAttachmentsRemainProofBearing ≡ true

canonicalRound381Boundary : Round381Boundary
canonicalRound381Boundary =
  round381-boundary true refl true refl true refl

round381FrontierRefinementLevel : ProofLevel
round381FrontierRefinementLevel = machineChecked

clayPromotion : Bool
clayPromotion = false

clayPromotionIsFalse : clayPromotion ≡ false
clayPromotionIsFalse = refl
