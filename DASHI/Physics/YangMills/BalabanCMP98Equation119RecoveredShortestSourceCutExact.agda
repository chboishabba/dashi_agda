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
-- The first remaining Round218 receipt has now been type-refined.  It is not a
-- same-typed equality between the old side-four selected fixture and the
-- Path13 background.  The genuine constructive target is to instantiate the
-- generic selected variational/physical background bridge directly on the
-- literal Path13 carrier, with selected links definitionally/same-object equal
-- to the Path13 links.
--
-- Thus the recovered source residual is exactly:
--
--   1. construct `SelectedPhysicalBackground13Instantiation`;
--   2. identify the perturbation bond-component/scalar-action coordinates with
--      the physical perturbation coordinates of the selected finite YM
--      action/IBP lane.
--
-- Neither producer is inhabited here.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanCMP98Equation119DisjunctivePhysicalSourceCutExact as Eq119Cut
import DASHI.Physics.YangMills.BalabanCMP98Equation120RecoveredSourceFrontierRound218Exact as R218
import DASHI.Physics.YangMills.BalabanPath13SelectedPhysicalBackgroundTargetExact as Path13Target

-- Public shape of the first recovered physical producer.
Path13SelectedPhysicalBackgroundProducer : Set → Set → Set₁
Path13SelectedPhysicalBackgroundProducer =
  Path13Target.SelectedPhysicalBackground13Instantiation

record RecoveredEq119ShortestSourceStatus : Set where
  field
    pointwiseSemanticFallbackCompilerClosed : Bool
    principalYFederbushIndexPruned : Bool
    selectedCutRadiusPrunedOnShortestRoute : Bool
    selectedPhysicalPeriodicRealizationPruned : Bool
    rawUnitPathRepresentationPruned : Bool
    path13PeriodicRealizationPruned : Bool

    path13SelectedPhysicalBackground13Constructed : Bool
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

    path13SelectedPhysicalBackground13ConstructedIsFalse :
      path13SelectedPhysicalBackground13Constructed ≡ false
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
  ; path13SelectedPhysicalBackground13Constructed = false
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
  ; path13SelectedPhysicalBackground13ConstructedIsFalse = refl
  ; perturbationCoordinateSemanticsClosedIsFalse = refl
  ; recoveredShortestPhysicalEq119SourceClosedIsFalse = refl
  }

-- Compatibility reading of the older Round218 prose coordinate.
path13BackgroundIsSelectedPhysicalBackgroundClosed :
  RecoveredEq119ShortestSourceStatus → Bool
path13BackgroundIsSelectedPhysicalBackgroundClosed =
  path13SelectedPhysicalBackground13Constructed

path13BackgroundIsSelectedPhysicalBackgroundClosedIsFalse :
  path13BackgroundIsSelectedPhysicalBackgroundClosed
    canonicalRecoveredEq119ShortestSourceStatus ≡ false
path13BackgroundIsSelectedPhysicalBackgroundClosedIsFalse =
  path13SelectedPhysicalBackground13ConstructedIsFalse
    canonicalRecoveredEq119ShortestSourceStatus

-- Imported proof-level receipts preserve archaeology provenance.
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

path13SelectedPhysicalBackgroundTargetLevel : ProofLevel
path13SelectedPhysicalBackgroundTargetLevel =
  Path13Target.cmp98Path13SelectedPhysicalBackgroundTargetLevel

literalCMP98RecoveredPath13BackgroundSameObjectLevel : ProofLevel
literalCMP98RecoveredPath13BackgroundSameObjectLevel =
  Path13Target.literalCMP98Path13SelectedPhysicalBackgroundProducerLevel

literalCMP98RecoveredPerturbationCoordinateSemanticsLevel : ProofLevel
literalCMP98RecoveredPerturbationCoordinateSemanticsLevel =
  R218.literalCMP98PerturbationCoordinateSemanticsRound218Level
