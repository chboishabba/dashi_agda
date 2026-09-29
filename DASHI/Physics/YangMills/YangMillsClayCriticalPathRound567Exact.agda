{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.YangMillsClayCriticalPathRound567Exact where

------------------------------------------------------------------------
-- GOAL-1 / ROUND567:
-- CRITICAL PATH WITH A3 FINITE-PROJECTION FACTORIZATION
--
-- R566 replaces the last abstract A3 "selected closure" language by the exact
-- physical statement:
--
--   every selected Wilson product factors through one finite projective
--   coordinate of the same continuum configuration system.
--
-- All representation and finite->continuum expectation transport after that
-- factorization is compiler/standard-owned.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat)
open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Physics.YangMills.YangMillsClayCriticalPathRound564Exact as R564
import DASHI.Physics.YangMills.YangMillsClayPreferredA3FiniteProjectionRound566Exact as A3

data CriticalFamily : Set where
  a3FiniteProjectiveWilson : CriticalFamily
  t1FiniteOSSameFamily : CriticalFamily
  t5LiteralCMP119Moments : CriticalFamily
  b1WilsonWEXT : CriticalFamily
  b2SameHamiltonian : CriticalFamily
  g1ActualCompactSimple : CriticalFamily
  h6SameFamilyWardKernel : CriticalFamily

criticalFamilyCount : Nat
criticalFamilyCount = 7

criticalLevel : CriticalFamily → ProofLevel
criticalLevel a3FiniteProjectiveWilson =
  A3.a3SelectedWilsonFiniteProjectionLevel
criticalLevel t1FiniteOSSameFamily =
  R564.criticalLevel R564.t1FiniteOSSameFamily
criticalLevel t5LiteralCMP119Moments =
  R564.criticalLevel R564.t5LiteralCMP119Moments
criticalLevel b1WilsonWEXT =
  R564.criticalLevel R564.b1WilsonWEXT
criticalLevel b2SameHamiltonian =
  R564.criticalLevel R564.b2SameHamiltonian
criticalLevel g1ActualCompactSimple =
  R564.criticalLevel R564.g1ActualCompactSimple
criticalLevel h6SameFamilyWardKernel =
  R564.criticalLevel R564.h6SameFamilyWardKernel

------------------------------------------------------------------------
-- A3 remaining physical payments.
------------------------------------------------------------------------

a3PositiveEventSemanticsLevel : ProofLevel
a3PositiveEventSemanticsLevel = A3.a3PositiveEventSemanticsLevel

a3EventBooleanAlgebraLevel : ProofLevel
a3EventBooleanAlgebraLevel = A3.a3EventBooleanAlgebraLevel

a3ProjectiveConsistencyLevel : ProofLevel
a3ProjectiveConsistencyLevel = A3.a3ProjectiveConsistencyLevel

a3ContinuityAtEmptyLevel : ProofLevel
a3ContinuityAtEmptyLevel = A3.a3ContinuityAtEmptyLevel

a3FiniteProjectionFactorizationLevel : ProofLevel
a3FiniteProjectionFactorizationLevel =
  A3.a3SelectedWilsonFiniteProjectionLevel

a3FiniteToRepresentedConvergenceCompilerLevel : ProofLevel
a3FiniteToRepresentedConvergenceCompilerLevel =
  A3.a3FiniteToRepresentedConvergenceCompilerLevel

round567CriticalPathCompilerLevel : ProofLevel
round567CriticalPathCompilerLevel = machineChecked
