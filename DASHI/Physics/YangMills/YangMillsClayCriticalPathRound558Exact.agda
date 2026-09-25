{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.YangMillsClayCriticalPathRound558Exact where

------------------------------------------------------------------------
-- GOAL-1 / ROUND558:
-- POST-R556 SOURCE-FIRST CLAY CRITICAL PATH
--
-- R555 still counted "continuum Wilson handoff" as an independent critical
-- family.  R556 removes that payment by constructing WEXT directly on the
-- exact CMP119/T5 selected covariance carrier.  R278 then compiles finite ->
-- continuum covariance convergence.
--
-- The shortest mass-gap/nontriviality path is now SEVEN source families:
--
--   1. A3 selected cylinder/Wilson representation
--   2. T1 finite/RG + finite-OS same-family source
--   3. T5 quantitative producer = literal CMP119 finite family
--   4. B1 source-first Wilson WEXT on that exact covariance carrier
--   5. B2 same reconstructed-H energy/decay coordinate
--   6. G1 actual compact-simple group + aligned quantitative source
--   7. H6 minimal same-family Gaussian/Ward kernel
--
-- The finite->continuum Wilson covariance step and half-rate transport are
-- compilers, not additional physical source families.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Nat using (Nat)

open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Physics.YangMills.YangMillsClayPostSelectedCylinderFrontierRound548Exact as A3
import DASHI.Physics.YangMills.YangMillsConcreteT1FiniteOSSourceRound545Exact as T1
import DASHI.Physics.YangMills.YangMillsConcreteQuantitativeOS05Round514Exact as T5
import DASHI.Physics.YangMills.YangMillsSourceFirstWilsonCovarianceRound556Exact as B1
import DASHI.Physics.YangMills.YangMillsSourceFirstWilsonMassGapRound557Exact as BGap
import DASHI.Physics.YangMills.BalabanWilsonWEXTMaxCutRound494Exact as WEXT
import DASHI.Physics.YangMills.YangMillsActualGroupCompleteSourceRound543Exact as G1
import DASHI.Physics.YangMills.YangMillsClayMinimalH6NontrivialityRound550Exact as H6
import DASHI.Physics.YangMills.YangMillsClayCPhysicalPackageMaxCutRound527Exact as C

data CriticalFamily : Set where
  a3SelectedRepresentation : CriticalFamily
  t1FiniteOSSameFamily : CriticalFamily
  t5QuantitativeSameFamily : CriticalFamily
  b1SourceFirstWilsonWEXT : CriticalFamily
  b2SameHamiltonian : CriticalFamily
  g1ActualCompactSimple : CriticalFamily
  h6MinimalWardNontriviality : CriticalFamily

criticalFamilyCount : Nat
criticalFamilyCount = 7

criticalLevel : CriticalFamily → ProofLevel
criticalLevel a3SelectedRepresentation =
  A3.a3SelectedObservableClosureRepresentationLevel
criticalLevel t1FiniteOSSameFamily =
  T1.literalRound545ConcreteT1FiniteOSSourceLevel
criticalLevel t5QuantitativeSameFamily =
  T5.literalRound514SameFiniteExpectationAttachmentLevel
criticalLevel b1SourceFirstWilsonWEXT =
  B1.literalRound556SourceFirstWilsonCarrierLevel
criticalLevel b2SameHamiltonian =
  BGap.literalRound557SameHamiltonianTransferLevel
criticalLevel g1ActualCompactSimple =
  G1.literalRound543ActualGroupCompleteSourceLevel
criticalLevel h6MinimalWardNontriviality =
  H6.literalRound550MinimalWardKernelLevel

------------------------------------------------------------------------
-- Internal critical subclaims.
------------------------------------------------------------------------

a3PositiveEventSemanticsLevel : ProofLevel
a3PositiveEventSemanticsLevel =
  A3.a3PositiveEventSemanticsLevel

a3BooleanAlgebraLevel : ProofLevel
a3BooleanAlgebraLevel =
  A3.a3EventBooleanAlgebraLevel

a3ProjectiveConsistencyLevel : ProofLevel
a3ProjectiveConsistencyLevel =
  A3.a3ProjectiveConsistencyLevel

a3ContinuityAtEmptyLevel : ProofLevel
a3ContinuityAtEmptyLevel =
  A3.a3ContinuityAtEmptyLevel

a3CylinderGeneratorRepresentationLevel : ProofLevel
a3CylinderGeneratorRepresentationLevel =
  A3.a3CylinderGeneratorRepresentationLevel

wextTwoMarkExpansionLevel : ProofLevel
wextTwoMarkExpansionLevel =
  WEXT.literalRound494WilsonTwoMarkExpansionLevel

wextConnectingWeightTailLevel : ProofLevel
wextConnectingWeightTailLevel =
  WEXT.literalRound494WilsonConnectingWeightTailLevel

finiteToContinuumWilsonCovarianceLevel : ProofLevel
finiteToContinuumWilsonCovarianceLevel =
  BGap.round557FiniteToContinuumCovarianceCompilerLevel

massGapCompilerLevel : ProofLevel
massGapCompilerLevel =
  BGap.round557MassGapCompilerLevel

minimalH6CompilerLevel : ProofLevel
minimalH6CompilerLevel =
  H6.round550MinimalH6CompilerLevel

------------------------------------------------------------------------
-- Critical-path exclusions.
------------------------------------------------------------------------

separateContinuumWilsonConvergenceFamilyRequired : Bool
separateContinuumWilsonConvergenceFamilyRequired = false

printedJRouteRequired : Bool
printedJRouteRequired = false

finiteHamiltonianMoscoRouteRequired : Bool
finiteHamiltonianMoscoRouteRequired = false

fullCLayerRequiredForMassGap : Bool
fullCLayerRequiredForMassGap = false

fullCLayerRequiredForMinimalH6 : Bool
fullCLayerRequiredForMinimalH6 = false

fullCLayerRetainedForConservativeClayExistence : Bool
fullCLayerRetainedForConservativeClayExistence = true

round558CriticalPathCompilerLevel : ProofLevel
round558CriticalPathCompilerLevel = machineChecked
