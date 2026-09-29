{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.YangMillsClayPreferredA3SelectedClassRound550Exact where

------------------------------------------------------------------------
-- GOAL-1 A3 / ROUND550:
-- AUTHORITATIVE SELECTED-CLASS CONTINUUM ROUTE
--
-- Supersedes the old R509/R510 all-observable dependency.
--
-- Preferred A3:
--
--   positive literal cylinder events
--     + event Boolean algebra
--     + projective expectation consistency
--     + continuity at empty
--       -> represented countably-additive projective measure
--       -> cylinder-generator representation (R547, compiler-owned)
--     + selected cylinder/Wilson closure theorem
--       -> selected limit expectation = represented integral
--       -> finite selected expectations converge to represented integral
--          (R549, compiler-owned)
--
-- Arbitrary Configuration -> Real representation is not a prerequisite.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Nat using (Nat)

open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Physics.YangMills.YangMillsClayIrreducibleSourceFamiliesRound546Exact as R546
import DASHI.Physics.YangMills.YangMillsPhysicalProjectiveCylinderRepresentationRound535Exact as R535
import DASHI.Physics.YangMills.YangMillsSelectedCylinderRepresentationRound547Exact as R547
import DASHI.Physics.YangMills.YangMillsSelectedRepresentedExpectationConvergenceRound549Exact as R549

preferredSourceFamilyCount : Nat
preferredSourceFamilyCount = R546.preferredSourceFamilyCount

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
  R549.literalRound549SelectedObservableClosureRepresentationLevel

a3FiniteSelectedToRepresentedConvergenceLevel : ProofLevel
a3FiniteSelectedToRepresentedConvergenceLevel =
  R549.round549SelectedRepresentedConvergenceCompilerLevel

oldR509AllObservablePathPreferred : Bool
oldR509AllObservablePathPreferred = false

arbitraryConfigurationObservableRepresentationRequired : Bool
arbitraryConfigurationObservableRepresentationRequired = false

finiteSelectedToRepresentedConvergenceStillPhysical : Bool
finiteSelectedToRepresentedConvergenceStillPhysical = false

selectedObservableClosureStillPhysical : Bool
selectedObservableClosureStillPhysical = true

a3PreferredOpenPhysicalSubclaimCount : Nat
a3PreferredOpenPhysicalSubclaimCount = 5

-- The five open A3 payments are:
--   1 positive event semantics
--   2 event Boolean algebra
--   3 projective consistency
--   4 continuity at empty
--   5 selected cylinder/Wilson closure representation
-- Generator representation and finite->represented convergence are compilers.

round550PreferredA3SchedulerLevel : ProofLevel
round550PreferredA3SchedulerLevel = machineChecked
