{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.YangMillsClayPreferredA3FiniteCylinderRound554Exact where

------------------------------------------------------------------------
-- GOAL-1 A3 / ROUND554:
-- PREFERRED A3 AFTER FINITE-CYLINDER CLOSURE REDUCTION
--
-- R553 replaces the broad selected-observable closure theorem by:
--
--   STANDARD:
--     finite cylinder functions integrate against the projective extension
--     according to their finite marginals;
--
--   YM-SPECIFIC:
--     every selected Wilson/cylinder observable consumed downstream is such a
--     finite-cylinder function of the SAME projective configuration.
--
-- Scalar-limit uniqueness then compiles
--
--   limitExpectation(F) = integral F dmu
--
-- and R549 compiles finite selected expectations -> represented integral.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Nat using (Nat)

open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Physics.YangMills.YangMillsClayPreferredA3SelectedClassRound550Exact as R550
import DASHI.Physics.YangMills.YangMillsSelectedCylinderFunctionClosureRound553Exact as R553
import DASHI.Physics.YangMills.YangMillsSelectedRepresentedExpectationConvergenceRound549Exact as R549

preferredSourceFamilyCount : Nat
preferredSourceFamilyCount = R550.preferredSourceFamilyCount

a3PositiveEventSemanticsLevel : ProofLevel
a3PositiveEventSemanticsLevel = R550.a3PositiveEventSemanticsLevel

a3EventBooleanAlgebraLevel : ProofLevel
a3EventBooleanAlgebraLevel = R550.a3EventBooleanAlgebraLevel

a3ProjectiveConsistencyLevel : ProofLevel
a3ProjectiveConsistencyLevel = R550.a3ProjectiveConsistencyLevel

a3ContinuityAtEmptyLevel : ProofLevel
a3ContinuityAtEmptyLevel = R550.a3ContinuityAtEmptyLevel

a3SelectedWilsonFiniteCylinderRealizationLevel : ProofLevel
a3SelectedWilsonFiniteCylinderRealizationLevel =
  R553.literalRound553SelectedWilsonFiniteCylinderRealizationLevel

a3FiniteCylinderProjectiveIntegrationLevel : ProofLevel
a3FiniteCylinderProjectiveIntegrationLevel =
  R553.round553ProjectiveCylinderFunctionConvergenceAuthorityLevel

a3SelectedLimitIntegralEqualityCompilerLevel : ProofLevel
a3SelectedLimitIntegralEqualityCompilerLevel =
  R553.round553SelectedClosureCompilerLevel

a3FiniteSelectedConvergenceCompilerLevel : ProofLevel
a3FiniteSelectedConvergenceCompilerLevel =
  R549.round549SelectedRepresentedConvergenceCompilerLevel

a3PreferredOpenPhysicalSubclaimCount : Nat
a3PreferredOpenPhysicalSubclaimCount = 5

generalLpCompletionRequired : Bool
generalLpCompletionRequired = false

prokhorovRequired : Bool
prokhorovRequired = false

arbitraryObservableRepresentationRequired : Bool
arbitraryObservableRepresentationRequired = false

round554PreferredA3FiniteCylinderSchedulerLevel : ProofLevel
round554PreferredA3FiniteCylinderSchedulerLevel = machineChecked
