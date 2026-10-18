{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.YangMillsClayCriticalPathRound572Exact where

------------------------------------------------------------------------
-- GOAL-1 / ROUND572:
-- CRITICAL PATH WITH SOURCE-FIRST ACTUAL-GROUP G1
--
-- This is R567 plus the R569--R571 all-group constructor refactor.
--
-- G1 no longer contains post-hoc equality obligations between a classification
-- quantitative package and the actual compact-simple group, nor between that
-- package and the five-block source.  Those are constructor facts.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat)
open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Physics.YangMills.YangMillsClayCriticalPathRound567Exact as R567
import DASHI.Physics.YangMills.YangMillsActualGroupSourceFirstCompleteRound571Exact as G1

data CriticalFamily : Set where
  a3FiniteProjectiveWilson : CriticalFamily
  t1FiniteOSSameFamily : CriticalFamily
  t5LiteralCMP119Moments : CriticalFamily
  b1WilsonWEXT : CriticalFamily
  b2SameHamiltonian : CriticalFamily
  g1SourceFirstActualGroup : CriticalFamily
  h6SameFamilyWardKernel : CriticalFamily

criticalFamilyCount : Nat
criticalFamilyCount = 7

criticalLevel : CriticalFamily → ProofLevel
criticalLevel a3FiniteProjectiveWilson =
  R567.criticalLevel R567.a3FiniteProjectiveWilson
criticalLevel t1FiniteOSSameFamily =
  R567.criticalLevel R567.t1FiniteOSSameFamily
criticalLevel t5LiteralCMP119Moments =
  R567.criticalLevel R567.t5LiteralCMP119Moments
criticalLevel b1WilsonWEXT =
  R567.criticalLevel R567.b1WilsonWEXT
criticalLevel b2SameHamiltonian =
  R567.criticalLevel R567.b2SameHamiltonian
criticalLevel g1SourceFirstActualGroup =
  G1.literalRound571SourceFirstActualGroupCompleteLevel
criticalLevel h6SameFamilyWardKernel =
  R567.criticalLevel R567.h6SameFamilyWardKernel

g1ActualCompactSimpleWitnessLevel : ProofLevel
g1ActualCompactSimpleWitnessLevel =
  G1.literalRound571ActualCompactSimpleWitnessLevel

g1ActualQuantitativeBoundsLevel : ProofLevel
g1ActualQuantitativeBoundsLevel =
  G1.literalRound571ActualQuantitativeBoundsLevel

g1FiveBlockPhysicalDataLevel : ProofLevel
g1FiveBlockPhysicalDataLevel =
  G1.literalRound571FiveBlockPhysicalDataLevel

g1AlignmentCompilerLevel : ProofLevel
g1AlignmentCompilerLevel =
  G1.round571SourceFirstAllGroupCompilerLevel

round572CriticalPathCompilerLevel : ProofLevel
round572CriticalPathCompilerLevel = machineChecked
