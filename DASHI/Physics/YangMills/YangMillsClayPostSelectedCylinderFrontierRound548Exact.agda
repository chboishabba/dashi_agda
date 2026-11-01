{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.YangMillsClayPostSelectedCylinderFrontierRound548Exact where

------------------------------------------------------------------------
-- GOAL-1 / ROUND548: POST-R547 PREFERRED SOURCE FRONTIER
--
-- The 14-family scheduler remains authoritative, but A3 is sharpened:
--
-- OLD over-strong source field:
--   limitExpectation F = integral F dmu
--   for every arbitrary Configuration -> Real.
--
-- NEW preferred boundary:
--   * positive literal cylinder-event semantics;
--   * Boolean-algebra laws on those literal events;
--   * projective probability consistency;
--   * continuity at empty for the whole projective family;
--   * machine-owned representation on each literal cylinder generator (R547);
--   * ONE remaining closure theorem extending generator representation to the
--     selected cylinder/Wilson observable algebra actually consumed downstream.
--
-- No claim is made for arbitrary bounded observables without such a closure
-- theorem.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Nat using (Nat)

open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Physics.YangMills.YangMillsClayIrreducibleSourceFamiliesRound546Exact as R546
import DASHI.Physics.YangMills.YangMillsPhysicalProjectiveCylinderRepresentationRound535Exact as R535
import DASHI.Physics.YangMills.YangMillsSelectedCylinderRepresentationRound547Exact as R547

preferredSourceFamilyCount : Nat
preferredSourceFamilyCount = R546.preferredSourceFamilyCount

------------------------------------------------------------------------
-- Sharpened A3 subcut.
------------------------------------------------------------------------

a3PositiveEventSemanticsLevel : ProofLevel
a3PositiveEventSemanticsLevel =
  R535.literalRound535CylinderEventIndicatorSemanticsLevel

a3EventBooleanAlgebraLevel : ProofLevel
a3EventBooleanAlgebraLevel =
  R535.literalRound535CylinderEventBooleanAlgebraLevel

a3ProjectiveConsistencyLevel : ProofLevel
a3ProjectiveConsistencyLevel =
  R535.literalRound535ProjectiveEventExpectationConsistencyLevel

a3ContinuityAtEmptyLevel : ProofLevel
a3ContinuityAtEmptyLevel =
  R535.literalRound535ProjectiveContinuityAtEmptyLevel

a3CylinderGeneratorRepresentationLevel : ProofLevel
a3CylinderGeneratorRepresentationLevel =
  R547.round547CylinderGeneratorRepresentationCompilerLevel

a3SelectedObservableClosureRepresentationLevel : ProofLevel
a3SelectedObservableClosureRepresentationLevel =
  R547.literalRound547SelectedObservableClosureRepresentationLevel

------------------------------------------------------------------------
-- The old all-observable representation premise is not on the preferred cut.
------------------------------------------------------------------------

arbitraryConfigurationObservableRepresentationRequired : Bool
arbitraryConfigurationObservableRepresentationRequired = false

literalCylinderGeneratorRepresentationAlreadyCompiled : Bool
literalCylinderGeneratorRepresentationAlreadyCompiled = true

selectedObservableClosureStillPhysical : Bool
selectedObservableClosureStillPhysical = true

preferredFamilyCountChangedByA3Sharpening : Bool
preferredFamilyCountChangedByA3Sharpening = false

opaqueEndpointPredicatesRemaining : Bool
opaqueEndpointPredicatesRemaining =
  R546.opaqueEndpointPredicatesRemaining

constructorChoiceEqualitiesRemaining : Bool
constructorChoiceEqualitiesRemaining =
  R546.constructorChoiceEqualitiesRemaining

round548PostSelectedCylinderFrontierCompilerLevel : ProofLevel
round548PostSelectedCylinderFrontierCompilerLevel = machineChecked
