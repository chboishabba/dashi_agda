{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.YangMillsClayPreferredA3FiniteProjectionRound566Exact where

------------------------------------------------------------------------
-- GOAL-1 A3 / ROUND566:
-- POST-R565 FINITE-PROJECTION A3 FRONTIER
--
-- R554 reduced the representation theorem to finite-cylinder realization.
-- R565 makes that meaning concrete:
--
--   selected Wilson observable
--       factors through one finite projective coordinate
--          -> standard finite-cylinder/projective integration theorem
--          -> selected limit expectation = represented integral
--          -> finite selected expectations converge to represented integral.
--
-- Therefore the five genuinely physical A3 payments are now:
--
--   A3a positive literal event semantics
--   A3b literal event Boolean algebra
--   A3c projective event expectation consistency
--   A3d projective continuity at empty
--   A3e selected Wilson finite-projection factorization
--
-- There is no arbitrary-observable, Lp-completion, Prokhorov, or selected
-- measure-equality payment on the preferred route.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false)
open import Agda.Builtin.Nat using (Nat)

open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Physics.YangMills.YangMillsClayPreferredA3FiniteCylinderRound554Exact as R554
import DASHI.Physics.YangMills.YangMillsSelectedWilsonFiniteProjectionRound565Exact as R565
import DASHI.Physics.YangMills.YangMillsSelectedCylinderFunctionClosureRound553Exact as R553
import DASHI.Physics.YangMills.YangMillsSelectedRepresentedExpectationConvergenceRound549Exact as R549

a3PositiveEventSemanticsLevel : ProofLevel
a3PositiveEventSemanticsLevel =
  R554.a3PositiveEventSemanticsLevel

a3EventBooleanAlgebraLevel : ProofLevel
a3EventBooleanAlgebraLevel =
  R554.a3EventBooleanAlgebraLevel

a3ProjectiveConsistencyLevel : ProofLevel
a3ProjectiveConsistencyLevel =
  R554.a3ProjectiveConsistencyLevel

a3ContinuityAtEmptyLevel : ProofLevel
a3ContinuityAtEmptyLevel =
  R554.a3ContinuityAtEmptyLevel

a3SelectedWilsonFiniteProjectionLevel : ProofLevel
a3SelectedWilsonFiniteProjectionLevel =
  R565.literalRound565SelectedWilsonFiniteProjectionFactorizationLevel

a3FiniteProjectionToCylinderCompilerLevel : ProofLevel
a3FiniteProjectionToCylinderCompilerLevel =
  R565.round565FiniteProjectionToCylinderCompilerLevel

a3SelectedLimitIntegralCompilerLevel : ProofLevel
a3SelectedLimitIntegralCompilerLevel =
  R553.round553SelectedClosureCompilerLevel

a3FiniteToRepresentedConvergenceCompilerLevel : ProofLevel
a3FiniteToRepresentedConvergenceCompilerLevel =
  R549.round549SelectedRepresentedConvergenceCompilerLevel

a3OpenPhysicalSubclaimCount : Nat
a3OpenPhysicalSubclaimCount = 5

arbitraryObservableRepresentationRequired : Bool
arbitraryObservableRepresentationRequired = false

generalLpCompletionRequired : Bool
generalLpCompletionRequired = false

prokhorovRequired : Bool
prokhorovRequired = false

postHocContinuumMeasureEqualityRequired : Bool
postHocContinuumMeasureEqualityRequired = false

round566PreferredA3FiniteProjectionSchedulerLevel : ProofLevel
round566PreferredA3FiniteProjectionSchedulerLevel = machineChecked
