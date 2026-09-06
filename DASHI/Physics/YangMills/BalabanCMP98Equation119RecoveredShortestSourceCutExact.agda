{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanCMP98Equation119RecoveredShortestSourceCutExact where

------------------------------------------------------------------------
-- CMP98 EQ. (119): RECOVERED SHORTEST SOURCE CUT AFTER ROUND218 ARCHAEOLOGY
--
-- The pointwise selected-cut route remains a valid semantic fallback, but
-- Round218 proves that it is not the shortest source frontier once the later
-- physical/dyadic/path13 owners are taken into account.
--
-- Already-owned coordinates:
--   * principal-Y / Federbush indexing (R179);
--   * dyadic physical principal-log admission without selected-cut-radius
--     comparison (R181);
--   * selected physical periodic realization (R187);
--   * raw/unit path homomorphism (R189);
--   * literal Path13 side-13 periodic realization (R192).
--
-- Therefore the recovered source residual is exactly two same-object receipts:
--
--   1. the Path13 physical background is the selected variational/physical
--      background used by the analytic estimates;
--   2. the perturbation bond-component/scalar-action coordinates are the same
--      physical perturbation coordinates used by the selected finite YM
--      action/IBP lane.
--
-- This file does not claim either receipt is inhabited.  It prevents older
-- global-cut or realization coordinates from being reopened as if they were
-- still highest-alpha payments.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanCMP98Equation119DisjunctivePhysicalSourceCutExact as Eq119Cut
import DASHI.Physics.YangMills.BalabanCMP98Equation120RecoveredSourceFrontierRound218Exact as R218

record RecoveredEq119ShortestSourceStatus : Set where
  field
    pointwiseSemanticFallbackCompilerClosed : Bool
    principalYFederbushIndexPruned : Bool
    selectedCutRadiusPrunedOnShortestRoute : Bool
    selectedPhysicalPeriodicRealizationPruned : Bool
    rawUnitPathRepresentationPruned : Bool
    path13PeriodicRealizationPruned : Bool

    path13BackgroundIsSelectedPhysicalBackgroundClosed : Bool
    perturbationCoordinateSemanticsClosed : Bool
    recoveredShortestPhysicalEq119SourceClosed : Bool

    pointwiseSemanticFallbackCompilerClosedIsTrue :
      pointwiseSemanticFallbackCompilerClosed ≡ true
    principalYFederbushIndexPrunedIsTrue :
      principalYFederbushIndexPruned ≡ true
    selectedCutRadiusPrunedOnShortestRouteIsTrue :
      selectedCutRadiusPrunedOnShortestRoute ≡ true
    selectedPhysicalPeriodicRealizationPrunedIsTrue :
      selectedPhysicalPeriodicRealizationPruned ≡ true
    rawUnitPathRepresentationPrunedIsTrue :
      rawUnitPathRepresentationPruned ≡ true
    path13PeriodicRealizationPrunedIsTrue :
      path13PeriodicRealizationPruned ≡ true

    path13BackgroundIsSelectedPhysicalBackgroundClosedIsFalse :
      path13BackgroundIsSelectedPhysicalBackgroundClosed ≡ false
    perturbationCoordinateSemanticsClosedIsFalse :
      perturbationCoordinateSemanticsClosed ≡ false
    recoveredShortestPhysicalEq119SourceClosedIsFalse :
      recoveredShortestPhysicalEq119SourceClosed ≡ false

open RecoveredEq119ShortestSourceStatus public

canonicalRecoveredEq119ShortestSourceStatus :
  RecoveredEq119ShortestSourceStatus
canonicalRecoveredEq119ShortestSourceStatus = record
  { pointwiseSemanticFallbackCompilerClosed =
      Eq119Cut.pointwiseSemanticSelectedCutCompilerClosed
        Eq119Cut.canonicalEq119DisjunctivePhysicalSourceStatus
  ; principalYFederbushIndexPruned = true
  ; selectedCutRadiusPrunedOnShortestRoute = true
  ; selectedPhysicalPeriodicRealizationPruned = true
  ; rawUnitPathRepresentationPruned = true
  ; path13PeriodicRealizationPruned = true
  ; path13BackgroundIsSelectedPhysicalBackgroundClosed = false
  ; perturbationCoordinateSemanticsClosed = false
  ; recoveredShortestPhysicalEq119SourceClosed = false
  ; pointwiseSemanticFallbackCompilerClosedIsTrue =
      Eq119Cut.pointwiseSemanticSelectedCutCompilerClosedIsTrue
        Eq119Cut.canonicalEq119DisjunctivePhysicalSourceStatus
  ; principalYFederbushIndexPrunedIsTrue = refl
  ; selectedCutRadiusPrunedOnShortestRouteIsTrue = refl
  ; selectedPhysicalPeriodicRealizationPrunedIsTrue = refl
  ; rawUnitPathRepresentationPrunedIsTrue = refl
  ; path13PeriodicRealizationPrunedIsTrue = refl
  ; path13BackgroundIsSelectedPhysicalBackgroundClosedIsFalse = refl
  ; perturbationCoordinateSemanticsClosedIsFalse = refl
  ; recoveredShortestPhysicalEq119SourceClosedIsFalse = refl
  }

-- The imported proof-level receipts make the pruning provenance explicit.
principalYFederbushIndexPruningLevel : ProofLevel
principalYFederbushIndexPruningLevel =
  R218.cmp98PrincipalYFrontierPrunedRound218Level

selectedCutRadiusPruningLevel : ProofLevel
selectedCutRadiusPruningLevel =
  R218.cmp98SelectedCutRadiusFrontierPrunedRound218Level

pathRealizationPruningLevel : ProofLevel
pathRealizationPruningLevel =
  R218.cmp98PathRealizationFrontierPrunedRound218Level

recoveredSourceFrontierLevel : ProofLevel
recoveredSourceFrontierLevel =
  R218.cmp98Equation120RecoveredSourceFrontierRound218Level

literalCMP98RecoveredPath13BackgroundSameObjectLevel : ProofLevel
literalCMP98RecoveredPath13BackgroundSameObjectLevel =
  R218.literalCMP98Path13SelectedPhysicalBackgroundSameObjectRound218Level

literalCMP98RecoveredPerturbationCoordinateSemanticsLevel : ProofLevel
literalCMP98RecoveredPerturbationCoordinateSemanticsLevel =
  R218.literalCMP98PerturbationCoordinateSemanticsRound218Level
