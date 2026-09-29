{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.YangMillsClayCriticalPathRound562Exact where

------------------------------------------------------------------------
-- GOAL-1 / ROUND562:
-- POST-R549/R553 + R556/R559/R560 CRITICAL PATH
--
-- This owner merges the newest source-first reductions into one Clay-facing
-- theorem scheduler:
--
--   A3  selected finite-cylinder projective representation
--       (no R499 all-observable premise; no Prokhorov detour)
--
--   T1  concrete finite/RG + published finite OS source on one family
--
--   T5  exponential moments constructed directly on literal CMP119
--       (no same-family expectation weld)
--
--   B1  source-first Wilson covariance on the exact CMP119/T5 carrier
--       with W1 reduced to literal Wilson mixed-log cluster expansion and
--       W3 the connecting-weight tail
--
--   B2  same reconstructed-H transfer-energy/decay coordinate
--
--   G1  actual compact-simple group witness + aligned quantitative package
--       + physical five-block source
--
--   H6  minimal same-family Gaussian/Ward nontriviality kernel.
--
-- Richer C/OPE/stress work remains off the mass-gap cut except where needed
-- for the conservative Clay local-field existence finish.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Nat using (Nat)

open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Physics.YangMills.YangMillsClayPreferredA3FiniteCylinderRound554Exact as A3
import DASHI.Physics.YangMills.YangMillsConcreteT1FiniteOSSourceRound545Exact as T1
import DASHI.Physics.YangMills.YangMillsLiteralCMP119QuantitativeMomentsRound559Exact as T5
import DASHI.Physics.YangMills.YangMillsLiteralCMP119OS05FromMomentsRound560Exact as OS05
import DASHI.Physics.YangMills.YangMillsSourceFirstWilsonCovarianceRound556Exact as B1
import DASHI.Physics.YangMills.YangMillsSourceFirstWilsonMassGapRound557Exact as BGap
import DASHI.Physics.YangMills.BalabanWilsonMixedLogClusterExpansionRound551Exact as W1
import DASHI.Physics.YangMills.BalabanWilsonWEXTFromMixedLogRound552Exact as WEXT
import DASHI.Physics.YangMills.YangMillsActualGroupCompleteSourceRound543Exact as G1
import DASHI.Physics.YangMills.YangMillsClayMinimalH6NontrivialityRound550Exact as H6
import DASHI.Physics.YangMills.YangMillsClayCPhysicalPackageMaxCutRound527Exact as C

data CriticalFamily : Set where
  a3SelectedFiniteCylinderRepresentation : CriticalFamily
  t1FiniteOSSameFamily : CriticalFamily
  t5LiteralCMP119Moments : CriticalFamily
  b1WilsonWEXT : CriticalFamily
  b2SameHamiltonian : CriticalFamily
  g1ActualCompactSimple : CriticalFamily
  h6MinimalWardNontriviality : CriticalFamily

criticalFamilyCount : Nat
criticalFamilyCount = 7

criticalLevel : CriticalFamily → ProofLevel
criticalLevel a3SelectedFiniteCylinderRepresentation =
  A3.a3SelectedWilsonFiniteCylinderRealizationLevel
criticalLevel t1FiniteOSSameFamily =
  T1.literalRound545ConcreteT1FiniteOSSourceLevel
criticalLevel t5LiteralCMP119Moments =
  T5.literalRound559CMP119ExponentialMomentProducerLevel
criticalLevel b1WilsonWEXT =
  B1.literalRound556SourceFirstWilsonCarrierLevel
criticalLevel b2SameHamiltonian =
  BGap.literalRound557SameHamiltonianTransferLevel
criticalLevel g1ActualCompactSimple =
  G1.literalRound543ActualGroupCompleteSourceLevel
criticalLevel h6MinimalWardNontriviality =
  H6.literalRound550MinimalWardKernelLevel

------------------------------------------------------------------------
-- A3 exact open/compiled boundary.
------------------------------------------------------------------------

a3PositiveEventSemanticsLevel : ProofLevel
a3PositiveEventSemanticsLevel = A3.a3PositiveEventSemanticsLevel

a3EventBooleanAlgebraLevel : ProofLevel
a3EventBooleanAlgebraLevel = A3.a3EventBooleanAlgebraLevel

a3ProjectiveConsistencyLevel : ProofLevel
a3ProjectiveConsistencyLevel = A3.a3ProjectiveConsistencyLevel

a3ContinuityAtEmptyLevel : ProofLevel
a3ContinuityAtEmptyLevel = A3.a3ContinuityAtEmptyLevel

a3FiniteCylinderRealizationLevel : ProofLevel
a3FiniteCylinderRealizationLevel =
  A3.a3SelectedWilsonFiniteCylinderRealizationLevel

a3SelectedLimitIntegralCompilerLevel : ProofLevel
a3SelectedLimitIntegralCompilerLevel =
  A3.a3SelectedLimitIntegralEqualityCompilerLevel

a3FiniteToRepresentedConvergenceCompilerLevel : ProofLevel
a3FiniteToRepresentedConvergenceCompilerLevel =
  A3.a3FiniteSelectedConvergenceCompilerLevel

------------------------------------------------------------------------
-- T5 exact source/closure boundary.
------------------------------------------------------------------------

t5LiteralMomentSourceLevel : ProofLevel
t5LiteralMomentSourceLevel =
  T5.literalRound559CMP119ExponentialMomentProducerLevel

t5FiniteOS05CompilerLevel : ProofLevel
t5FiniteOS05CompilerLevel =
  OS05.round560FiniteOS05FromLiteralMomentsLevel

t5CanonicalClosureAuthorityLevel : ProofLevel
t5CanonicalClosureAuthorityLevel =
  OS05.round560CanonicalClosureAuthorityLevel

t5SameFamilyExpectationAttachmentRequired : Bool
t5SameFamilyExpectationAttachmentRequired =
  T5.round559SameFiniteExpectationAttachmentRequired

------------------------------------------------------------------------
-- B exact source/compiled boundary.
------------------------------------------------------------------------

w1WilsonMixedLogClusterExpansionLevel : ProofLevel
w1WilsonMixedLogClusterExpansionLevel =
  W1.literalRound551WilsonMixedLogClusterExpansionLevel

w1CovarianceIdentityCompilerLevel : ProofLevel
w1CovarianceIdentityCompilerLevel =
  W1.round551WilsonCovarianceExpansionCompilerLevel

w3ConnectingWeightTailLevel : ProofLevel
w3ConnectingWeightTailLevel =
  WEXT.literalRound552ConnectingWeightTailLevel

finiteToContinuumWilsonCovarianceCompilerLevel : ProofLevel
finiteToContinuumWilsonCovarianceCompilerLevel =
  BGap.round557FiniteToContinuumCovarianceCompilerLevel

massGapCompilerLevel : ProofLevel
massGapCompilerLevel =
  BGap.round557MassGapCompilerLevel

sameHamiltonianTransferLevel : ProofLevel
sameHamiltonianTransferLevel =
  BGap.literalRound557SameHamiltonianTransferLevel

------------------------------------------------------------------------
-- G1/H6 and conservative local-field finish.
------------------------------------------------------------------------

allGroupStructuralWitnessLevel : ProofLevel
allGroupStructuralWitnessLevel =
  G1.round543StructuralWitnessLevel

allGroupActualAlignmentLevel : ProofLevel
allGroupActualAlignmentLevel =
  G1.round543ActualGroupAlignmentLevel

allGroupFiveBlockSourceLevel : ProofLevel
allGroupFiveBlockSourceLevel =
  G1.round543FiveBlockSourceMapLevel

minimalH6CompilerLevel : ProofLevel
minimalH6CompilerLevel =
  H6.round550MinimalH6CompilerLevel

fullCLayerRequiredForMassGap : Bool
fullCLayerRequiredForMassGap = false

fullCLayerRequiredForMinimalH6 : Bool
fullCLayerRequiredForMinimalH6 = false

fullCLayerRetainedForConservativeClayExistence : Bool
fullCLayerRetainedForConservativeClayExistence = true

oldR499AllObservableRouteRequired : Bool
oldR499AllObservableRouteRequired = false

prokhorovRouteRequired : Bool
prokhorovRouteRequired = false

printedJRouteRequired : Bool
printedJRouteRequired = false

finiteHamiltonianMoscoRouteRequired : Bool
finiteHamiltonianMoscoRouteRequired = false

round562CriticalPathCompilerLevel : ProofLevel
round562CriticalPathCompilerLevel = machineChecked
