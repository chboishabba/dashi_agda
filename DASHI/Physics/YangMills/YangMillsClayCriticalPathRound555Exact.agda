{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.YangMillsClayCriticalPathRound555Exact where

------------------------------------------------------------------------
-- GOAL-1 / ROUND555: CLAY CRITICAL PATH AFTER R547/R553/R550
--
-- This is NOT a replacement for the full 14-family R546 existence ledger.
-- It is the shortest theorem chain that produces the represented continuum,
-- continuum Wilson clustering, a positive gap on the SAME reconstructed H,
-- and same-system interacting/non-Gaussianity.
--
-- Critical path:
--
--   A3 selected cylinder/Wilson representation
--     -> T1/T5 same finite-family OS provenance
--     -> Wilson WEXT
--     -> same-family continuum Wilson clustering
--     -> SAME-H spectral coordinate
--     -> positive physical gap
--     -> actual compact-simple G source
--     -> minimal Ward/Gaussian same-H contradiction
--     -> interacting witness.
--
-- The richer curvature/OPE/stress C layer is retained separately for the
-- conservative Clay local-field existence standard, but is not a prerequisite
-- of the mass-gap/nontriviality reductio itself.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Nat using (Nat)

open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Physics.YangMills.YangMillsClayPostSelectedCylinderFrontierRound548Exact as A3
import DASHI.Physics.YangMills.YangMillsConcreteT1FiniteOSSourceRound545Exact as T1
import DASHI.Physics.YangMills.YangMillsConcreteQuantitativeOS05Round514Exact as T5
import DASHI.Physics.YangMills.BalabanWilsonWEXTMaxCutRound494Exact as WEXT
import DASHI.Physics.YangMills.YangMillsWilsonContinuumClusteringRound551Exact as WilsonContinuum
import DASHI.Physics.YangMills.YangMillsWilsonSameHMassGapRound552Exact as SameH
import DASHI.Physics.YangMills.YangMillsWilsonMassGapCriticalPathRound553Exact as GapPath
import DASHI.Physics.YangMills.YangMillsActualGroupCompleteSourceRound543Exact as AllG
import DASHI.Physics.YangMills.YangMillsClayMinimalH6NontrivialityRound550Exact as H6
import DASHI.Physics.YangMills.YangMillsClayCPhysicalPackageMaxCutRound527Exact as C

data CriticalFamily : Set where
  a3SelectedRepresentation : CriticalFamily
  t1FiniteOSSameFamily : CriticalFamily
  t5QuantitativeSameFamily : CriticalFamily
  b1WilsonWEXT : CriticalFamily
  b1ContinuumWilsonHandoff : CriticalFamily
  b2SameHamiltonian : CriticalFamily
  g1ActualCompactSimple : CriticalFamily
  h6MinimalWardNontriviality : CriticalFamily

criticalFamilyCount : Nat
criticalFamilyCount = 8

criticalLevel : CriticalFamily → ProofLevel
criticalLevel a3SelectedRepresentation =
  A3.a3SelectedObservableClosureRepresentationLevel
criticalLevel t1FiniteOSSameFamily =
  T1.literalRound545ConcreteT1FiniteOSSourceLevel
criticalLevel t5QuantitativeSameFamily =
  T5.literalRound514SameFiniteExpectationAttachmentLevel
criticalLevel b1WilsonWEXT =
  conditional
criticalLevel b1ContinuumWilsonHandoff =
  WilsonContinuum.literalRound551SameFamilyWilsonCorrelationConvergenceLevel
criticalLevel b2SameHamiltonian =
  SameH.literalRound552SameHamiltonianTransferCoordinateLevel
criticalLevel g1ActualCompactSimple =
  AllG.literalRound543ActualGroupCompleteSourceLevel
criticalLevel h6MinimalWardNontriviality =
  H6.literalRound550MinimalWardKernelLevel

------------------------------------------------------------------------
-- Internal critical subclaims kept visible.
------------------------------------------------------------------------

a3EventSemanticsLevel : ProofLevel
a3EventSemanticsLevel = A3.a3PositiveEventSemanticsLevel

a3BooleanAlgebraLevel : ProofLevel
a3BooleanAlgebraLevel = A3.a3EventBooleanAlgebraLevel

a3ProjectiveConsistencyLevel : ProofLevel
a3ProjectiveConsistencyLevel = A3.a3ProjectiveConsistencyLevel

a3ContinuityAtEmptyLevel : ProofLevel
a3ContinuityAtEmptyLevel = A3.a3ContinuityAtEmptyLevel

a3CylinderGeneratorRepresentationLevel : ProofLevel
a3CylinderGeneratorRepresentationLevel =
  A3.a3CylinderGeneratorRepresentationLevel

wextTwoMarkExpansionLevel : ProofLevel
wextTwoMarkExpansionLevel =
  WEXT.literalRound494WilsonTwoMarkExpansionLevel

wextConnectingWeightTailLevel : ProofLevel
wextConnectingWeightTailLevel =
  WEXT.literalRound494WilsonConnectingWeightTailLevel

wilsonContinuumTimeDistanceLevel : ProofLevel
wilsonContinuumTimeDistanceLevel =
  WilsonContinuum.literalRound551WilsonTimeDistanceMeaningLevel

massGapCompilerLevel : ProofLevel
massGapCompilerLevel =
  GapPath.round553MassGapCompilerLevel

minimalH6CompilerLevel : ProofLevel
minimalH6CompilerLevel =
  H6.round550MinimalH6CompilerLevel

------------------------------------------------------------------------
-- Conservative Clay local-field finish remains required, but off the gap cut.
------------------------------------------------------------------------

c1MarkedCurvatureLevel : ProofLevel
c1MarkedCurvatureLevel = C.c1MarkedCurvatureFamilyLevel

c2PhysicalOPERemainderLevel : ProofLevel
c2PhysicalOPERemainderLevel = C.c2PhysicalRemainderSharedTailLevel

c3AFRecurrenceLevel : ProofLevel
c3AFRecurrenceLevel = C.c3OneStepAFRecurrenceIdentificationLevel

c4DensityAnchoredStressLevel : ProofLevel
c4DensityAnchoredStressLevel = C.c4DensityAnchoredStressLaneLevel

fullCLayerRequiredForMassGapCompiler : Bool
fullCLayerRequiredForMassGapCompiler = false

fullCLayerRequiredForMinimalH6Contradiction : Bool
fullCLayerRequiredForMinimalH6Contradiction = false

fullCLayerRetainedForConservativeClayLocalFieldExistence : Bool
fullCLayerRetainedForConservativeClayLocalFieldExistence = true

printedJRouteRequired : Bool
printedJRouteRequired = false

finiteHamiltonianMoscoRouteRequired : Bool
finiteHamiltonianMoscoRouteRequired = false

round555CriticalPathCompilerLevel : ProofLevel
round555CriticalPathCompilerLevel = machineChecked
