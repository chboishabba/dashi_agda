{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.YangMillsClayCriticalPathRound564Exact where

------------------------------------------------------------------------
-- GOAL-1 / ROUND564:
-- SEVEN-FAMILY CRITICAL PATH WITH NARROW H6 SOURCE
--
-- R562 already owns the newest A3/T1/T5/B/G reductions.
-- R563 removes the last unnecessary local-QFT payload from H6:
--
--   H6 physical input =
--     SAME-family Gaussian -> local two-derivative Ward kernel.
--
-- OPE coefficients, OPE remainder and stress tensor are NOT prerequisites of
-- the mass-gap/nontriviality compiler.  They remain on the conservative
-- Jaffe--Witten local-field existence finish.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Nat using (Nat)

open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Physics.YangMills.YangMillsClayCriticalPathRound562Exact as R562
import DASHI.Physics.YangMills.YangMillsSameFamilyWardKernelSourceRound563Exact as Ward

data CriticalFamily : Set where
  a3SelectedFiniteCylinderRepresentation : CriticalFamily
  t1FiniteOSSameFamily : CriticalFamily
  t5LiteralCMP119Moments : CriticalFamily
  b1WilsonWEXT : CriticalFamily
  b2SameHamiltonian : CriticalFamily
  g1ActualCompactSimple : CriticalFamily
  h6SameFamilyWardKernel : CriticalFamily

criticalFamilyCount : Nat
criticalFamilyCount = 7

criticalLevel : CriticalFamily → ProofLevel
criticalLevel a3SelectedFiniteCylinderRepresentation =
  R562.criticalLevel R562.a3SelectedFiniteCylinderRepresentation
criticalLevel t1FiniteOSSameFamily =
  R562.criticalLevel R562.t1FiniteOSSameFamily
criticalLevel t5LiteralCMP119Moments =
  R562.criticalLevel R562.t5LiteralCMP119Moments
criticalLevel b1WilsonWEXT =
  R562.criticalLevel R562.b1WilsonWEXT
criticalLevel b2SameHamiltonian =
  R562.criticalLevel R562.b2SameHamiltonian
criticalLevel g1ActualCompactSimple =
  R562.criticalLevel R562.g1ActualCompactSimple
criticalLevel h6SameFamilyWardKernel =
  Ward.literalRound563SameFamilyWardKernelSourceLevel

------------------------------------------------------------------------
-- Compiler-owned H6 transport.
------------------------------------------------------------------------

h6WardAdapterLevel : ProofLevel
h6WardAdapterLevel =
  Ward.round563MinimalWardAdapterLevel

h6OPECoefficientRequired : Bool
h6OPECoefficientRequired =
  Ward.round563OPECoefficientRequiredForH6

h6OPERemainderRequired : Bool
h6OPERemainderRequired =
  Ward.round563OPERemainderRequiredForH6

h6StressTensorRequired : Bool
h6StressTensorRequired =
  Ward.round563StressTensorRequiredForH6

------------------------------------------------------------------------
-- Re-export the newest critical compiler coordinates.
------------------------------------------------------------------------

a3SelectedLimitIntegralCompilerLevel : ProofLevel
a3SelectedLimitIntegralCompilerLevel =
  R562.a3SelectedLimitIntegralCompilerLevel

a3FiniteToRepresentedConvergenceCompilerLevel : ProofLevel
a3FiniteToRepresentedConvergenceCompilerLevel =
  R562.a3FiniteToRepresentedConvergenceCompilerLevel

t5FiniteOS05CompilerLevel : ProofLevel
t5FiniteOS05CompilerLevel =
  R562.t5FiniteOS05CompilerLevel

w1CovarianceIdentityCompilerLevel : ProofLevel
w1CovarianceIdentityCompilerLevel =
  R562.w1CovarianceIdentityCompilerLevel

finiteToContinuumWilsonCovarianceCompilerLevel : ProofLevel
finiteToContinuumWilsonCovarianceCompilerLevel =
  R562.finiteToContinuumWilsonCovarianceCompilerLevel

massGapCompilerLevel : ProofLevel
massGapCompilerLevel =
  R562.massGapCompilerLevel

------------------------------------------------------------------------
-- Route firewalls.
------------------------------------------------------------------------

fullCLayerRequiredForMassGap : Bool
fullCLayerRequiredForMassGap = false

fullCLayerRequiredForH6 : Bool
fullCLayerRequiredForH6 = false

fullCLayerRetainedForConservativeClayExistence : Bool
fullCLayerRetainedForConservativeClayExistence = true

oldAllObservableRepresentationRouteRequired : Bool
oldAllObservableRepresentationRouteRequired = false

prokhorovRouteRequired : Bool
prokhorovRouteRequired = false

printedJRouteRequired : Bool
printedJRouteRequired = false

finiteHamiltonianMoscoRouteRequired : Bool
finiteHamiltonianMoscoRouteRequired = false

round564CriticalPathCompilerLevel : ProofLevel
round564CriticalPathCompilerLevel = machineChecked
