{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanCMP98Equation119RecoveredShortestSourceCutExact where

------------------------------------------------------------------------
-- CMP98 EQ. (119): RECOVERED SHORTEST SOURCE CUT AFTER ROUND218 ARCHAEOLOGY
--
-- The pointwise selected-cut route remains a valid semantic fallback, but the
-- later physical/dyadic/Path13 owners remove several older source coordinates.
--
-- IMPORTANT INDEX REPAIR:
-- the historical periodic APIs are predecessor-indexed:
--
--   PeriodicBlock n = periodicTorus4Definition (suc n),
--   PeriodicBondField n = BondField (suc n).
--
-- Physical side 13 therefore uses historical n=12.  R192/R193/R216 encode
-- this explicitly.  The Path13 realization is counted as pruned only together
-- with that repair; the superseded n=13 specialization must not be revived.
--
-- The two surviving source receipts remain:
--   1. construct the selected variational/physical background directly on the
--      literal Path13 background carrier;
--   2. rebuild the global/local Eq.(119) perturbation semantics so global Q'
--      acts on the bond-indexed Path13 field while local R0 values live in the
--      SU(2) Lie carrier, with literal scalar action on that local carrier.
--
-- Inside (2), both positive and signed bond projection are now constructed.
-- The negative occurrence uses the exact -Ad_{U^-1} rule on the repaired
-- side-13 rational background before the existing rational->real Lie compiler.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanCMP98Equation119DisjunctivePhysicalSourceCutExact as Eq119Cut
import DASHI.Physics.YangMills.BalabanCMP98Equation120RecoveredSourceFrontierRound218Exact as R218
import DASHI.Physics.YangMills.BalabanCMP98Path13PhysicalPeriodicRealizationRound192Exact as R192
import DASHI.Physics.YangMills.BalabanPath13SelectedPhysicalBackgroundTargetExact as Path13Target
import DASHI.Physics.YangMills.BalabanCMP98Path13PerturbationCarrierWeldExact as PerturbationTarget

Path13SelectedPhysicalBackgroundProducer : Set → Set → Set₁
Path13SelectedPhysicalBackgroundProducer =
  Path13Target.SelectedPhysicalBackground13Instantiation

Path13PerturbationCoordinateProducer : Set₁
Path13PerturbationCoordinateProducer =
  PerturbationTarget.Path13GlobalLocalPerturbationSemantics

record RecoveredEq119ShortestSourceStatus : Set where
  field
    pointwiseSemanticFallbackCompilerClosed : Bool
    principalYFederbushIndexPruned : Bool
    selectedCutRadiusPrunedOnShortestRoute : Bool
    selectedPhysicalPeriodicRealizationPruned : Bool
    rawUnitPathRepresentationPruned : Bool
    path13HistoricalPeriodicIndexRepairClosed : Bool
    path13PeriodicRealizationPruned : Bool

    path13PositiveBondPerturbationProjectionClosed : Bool
    path13RationalSignedBondPerturbationProjectionClosed : Bool
    path13SelectedPhysicalBackground13Constructed : Bool
    path13GlobalLocalPerturbationSemanticsConstructed : Bool
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
    path13HistoricalPeriodicIndexRepairClosedIsTrue :
      path13HistoricalPeriodicIndexRepairClosed ≡ true
    path13PeriodicRealizationPrunedIsTrue :
      path13PeriodicRealizationPruned ≡ true
    path13PositiveBondPerturbationProjectionClosedIsTrue :
      path13PositiveBondPerturbationProjectionClosed ≡ true
    path13RationalSignedBondPerturbationProjectionClosedIsTrue :
      path13RationalSignedBondPerturbationProjectionClosed ≡ true

    path13SelectedPhysicalBackground13ConstructedIsFalse :
      path13SelectedPhysicalBackground13Constructed ≡ false
    path13GlobalLocalPerturbationSemanticsConstructedIsFalse :
      path13GlobalLocalPerturbationSemanticsConstructed ≡ false
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
  ; path13HistoricalPeriodicIndexRepairClosed = true
  ; path13PeriodicRealizationPruned = true
  ; path13PositiveBondPerturbationProjectionClosed = true
  ; path13RationalSignedBondPerturbationProjectionClosed = true
  ; path13SelectedPhysicalBackground13Constructed = false
  ; path13GlobalLocalPerturbationSemanticsConstructed = false
  ; recoveredShortestPhysicalEq119SourceClosed = false
  ; pointwiseSemanticFallbackCompilerClosedIsTrue =
      Eq119Cut.pointwiseSemanticSelectedCutCompilerClosedIsTrue
        Eq119Cut.canonicalEq119DisjunctivePhysicalSourceStatus
  ; principalYFederbushIndexPrunedIsTrue = refl
  ; selectedCutRadiusPrunedOnShortestRouteIsTrue = refl
  ; selectedPhysicalPeriodicRealizationPrunedIsTrue = refl
  ; rawUnitPathRepresentationPrunedIsTrue = refl
  ; path13HistoricalPeriodicIndexRepairClosedIsTrue = refl
  ; path13PeriodicRealizationPrunedIsTrue = refl
  ; path13PositiveBondPerturbationProjectionClosedIsTrue = refl
  ; path13RationalSignedBondPerturbationProjectionClosedIsTrue = refl
  ; path13SelectedPhysicalBackground13ConstructedIsFalse = refl
  ; path13GlobalLocalPerturbationSemanticsConstructedIsFalse = refl
  ; recoveredShortestPhysicalEq119SourceClosedIsFalse = refl
  }

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

perturbationCoordinateSemanticsClosed :
  RecoveredEq119ShortestSourceStatus → Bool
perturbationCoordinateSemanticsClosed =
  path13GlobalLocalPerturbationSemanticsConstructed

perturbationCoordinateSemanticsClosedIsFalse :
  perturbationCoordinateSemanticsClosed
    canonicalRecoveredEq119ShortestSourceStatus ≡ false
perturbationCoordinateSemanticsClosedIsFalse =
  path13GlobalLocalPerturbationSemanticsConstructedIsFalse
    canonicalRecoveredEq119ShortestSourceStatus

principalYFederbushIndexPruningLevel : ProofLevel
principalYFederbushIndexPruningLevel =
  R218.cmp98PrincipalYFrontierPrunedRound218Level

selectedCutRadiusPruningLevel : ProofLevel
selectedCutRadiusPruningLevel =
  R218.cmp98SelectedCutRadiusFrontierPrunedRound218Level

path13HistoricalPeriodicIndexRepairLevel : ProofLevel
path13HistoricalPeriodicIndexRepairLevel =
  R192.cmp98Path13PhysicalPeriodicIndexRepairRound192Level

pathRealizationPruningLevel : ProofLevel
pathRealizationPruningLevel =
  R218.cmp98PathRealizationFrontierPrunedRound218Level

recoveredSourceFrontierLevel : ProofLevel
recoveredSourceFrontierLevel =
  R218.cmp98Equation120RecoveredSourceFrontierRound218Level

path13SelectedPhysicalBackgroundTargetLevel : ProofLevel
path13SelectedPhysicalBackgroundTargetLevel =
  Path13Target.cmp98Path13SelectedPhysicalBackgroundTargetLevel

path13PositiveBondPerturbationProjectionLevel : ProofLevel
path13PositiveBondPerturbationProjectionLevel =
  PerturbationTarget.cmp98Path13PositiveBondPerturbationProjectionLevel

path13RationalSignedBondPerturbationProjectionLevel : ProofLevel
path13RationalSignedBondPerturbationProjectionLevel =
  PerturbationTarget.cmp98Path13RationalSignedBondProjectionLevel

literalCMP98RecoveredPath13BackgroundSameObjectLevel : ProofLevel
literalCMP98RecoveredPath13BackgroundSameObjectLevel =
  Path13Target.literalCMP98Path13SelectedPhysicalBackgroundProducerLevel

literalCMP98RecoveredPerturbationCoordinateSemanticsLevel : ProofLevel
literalCMP98RecoveredPerturbationCoordinateSemanticsLevel =
  PerturbationTarget.literalCMP98Path13GlobalLocalPerturbationSemanticsLevel
