{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.YangMillsClayCriticalPathRound578Exact where

------------------------------------------------------------------------
-- GOAL-1 / ROUND578:
-- SHORTEST SOURCE-NATIVE CLAY THEOREM-COMPLETION PATH
--
-- This is the post-R568/R571/R576/R577 critical path.
--
-- PRIMARY:
--
--   A3  whole-projective measure + selected Wilson finite projection
--   T1  finite CMP119 / published finite OS applicability
--   T5  literal CMP119 quantitative moment producer
--   B1  Wilson mixed-log cluster expansion + connecting-weight tail
--   B2  transfer-energy/decay coordinate OF the reconstructed OS Hamiltonian
--   G1  actual compact-simple source-first quantitative/five-block construction
--   H6  narrow same-family Gaussian Ward kernel for nontriviality
--
-- Local OPE/stress enrichment remains on the conservative Clay-existence
-- finish, but is not a prerequisite of the shortest mass-gap/nontriviality
-- route.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false)
open import Agda.Builtin.Nat using (Nat)

open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Physics.YangMills.YangMillsClayPreferredA3FiniteProjectionRound566Exact as A3
import DASHI.Physics.YangMills.YangMillsWilsonPathFiniteFactorizationRound568Exact as A3Path
import DASHI.Physics.YangMills.YangMillsConcreteT1FiniteOSSourceRound545Exact as T1
import DASHI.Physics.YangMills.YangMillsLiteralCMP119QuantitativeMomentsRound559Exact as T5
import DASHI.Physics.YangMills.YangMillsLiteralCMP119OS05FromMomentsRound560Exact as OS05
import DASHI.Physics.YangMills.YangMillsPreferredWilsonWEXTSourceRound576Exact as B1
import DASHI.Physics.YangMills.YangMillsPreferredSameHamiltonianTransferRound577Exact as B2
import DASHI.Physics.YangMills.YangMillsActualGroupSourceFirstCompleteRound571Exact as G1
import DASHI.Physics.YangMills.YangMillsSameFamilyWardKernelSourceRound563Exact as H6

data CriticalFamily : Set where
  a3ProjectiveWilson : CriticalFamily
  t1FiniteOSSameFamily : CriticalFamily
  t5LiteralCMP119Moments : CriticalFamily
  b1WilsonWEXT : CriticalFamily
  b2ReconstructedHamiltonianTransfer : CriticalFamily
  g1ActualCompactSimple : CriticalFamily
  h6SameFamilyWardKernel : CriticalFamily

criticalFamilyCount : Nat
criticalFamilyCount = 7

criticalLevel : CriticalFamily → ProofLevel
criticalLevel a3ProjectiveWilson =
  A3.a3SelectedWilsonFiniteProjectionLevel
criticalLevel t1FiniteOSSameFamily =
  T1.literalRound545ConcreteT1FiniteOSSourceLevel
criticalLevel t5LiteralCMP119Moments =
  T5.literalRound559CMP119ExponentialMomentProducerLevel
criticalLevel b1WilsonWEXT =
  conditional
criticalLevel b2ReconstructedHamiltonianTransfer =
  B2.literalRound577TransferCoordinateOfReconstructedHamiltonianLevel
criticalLevel g1ActualCompactSimple =
  G1.literalRound571SourceFirstActualGroupCompleteLevel
criticalLevel h6SameFamilyWardKernel =
  H6.literalRound563SameFamilyWardKernelSourceLevel

------------------------------------------------------------------------
-- A3 exact open source payments.
------------------------------------------------------------------------

a3PositiveEventSemanticsLevel : ProofLevel
a3PositiveEventSemanticsLevel =
  A3.a3PositiveEventSemanticsLevel

a3EventBooleanAlgebraLevel : ProofLevel
a3EventBooleanAlgebraLevel =
  A3.a3EventBooleanAlgebraLevel

a3ProjectiveConsistencyLevel : ProofLevel
a3ProjectiveConsistencyLevel =
  A3.a3ProjectiveConsistencyLevel

a3ContinuityAtEmptyLevel : ProofLevel
a3ContinuityAtEmptyLevel =
  A3.a3ContinuityAtEmptyLevel

-- R568 proves finite path-value factorization generically.  What remains is
-- that those finite path coordinates are coordinates of the SAME selected
-- projective continuum system.
a3WilsonPathProjectionBelongsToProjectiveSystemLevel : ProofLevel
a3WilsonPathProjectionBelongsToProjectiveSystemLevel =
  A3Path.literalRound568PathProjectionBelongsToSelectedProjectiveSystemLevel

a3WilsonPathFactorizationCompilerLevel : ProofLevel
a3WilsonPathFactorizationCompilerLevel =
  A3Path.round568WilsonPathFactorizationCompilerLevel

a3FiniteToRepresentedConvergenceCompilerLevel : ProofLevel
a3FiniteToRepresentedConvergenceCompilerLevel =
  A3.a3FiniteToRepresentedConvergenceCompilerLevel

------------------------------------------------------------------------
-- T5 exact source payment.
------------------------------------------------------------------------

t5LiteralMomentProducerLevel : ProofLevel
t5LiteralMomentProducerLevel =
  T5.literalRound559CMP119ExponentialMomentProducerLevel

t5FiniteOS05CompilerLevel : ProofLevel
t5FiniteOS05CompilerLevel =
  OS05.round560FiniteOS05FromLiteralMomentsLevel

t5OS05ClosureAuthorityLevel : ProofLevel
t5OS05ClosureAuthorityLevel =
  OS05.round560CanonicalClosureAuthorityLevel

------------------------------------------------------------------------
-- B1 exact source payments.
------------------------------------------------------------------------

b1WilsonMixedLogClusterExpansionLevel : ProofLevel
b1WilsonMixedLogClusterExpansionLevel =
  B1.literalRound576WilsonMixedLogClusterExpansionLevel

b1ConnectingWeightTailLevel : ProofLevel
b1ConnectingWeightTailLevel =
  B1.literalRound576ConnectingWeightTailLevel

b1MagnitudeCalibrationPhysicalInputRequired : Bool
b1MagnitudeCalibrationPhysicalInputRequired =
  B1.round576MagnitudeCalibrationPhysicalInputRequired

b1WEXTCompilerLevel : ProofLevel
b1WEXTCompilerLevel =
  B1.round576PreferredWEXTCompilerLevel

------------------------------------------------------------------------
-- B2 exact source payment.
------------------------------------------------------------------------

b2TransferCoordinateOfReconstructedHamiltonianLevel : ProofLevel
b2TransferCoordinateOfReconstructedHamiltonianLevel =
  B2.literalRound577TransferCoordinateOfReconstructedHamiltonianLevel

b2PostHocHamiltonianEqualityRequired : Bool
b2PostHocHamiltonianEqualityRequired =
  B2.postHocHamiltonianEqualityRequired

------------------------------------------------------------------------
-- G1 exact source payments.
------------------------------------------------------------------------

g1ActualCompactSimpleWitnessLevel : ProofLevel
g1ActualCompactSimpleWitnessLevel =
  G1.literalRound571ActualCompactSimpleWitnessLevel

g1ActualQuantitativeBoundsLevel : ProofLevel
g1ActualQuantitativeBoundsLevel =
  G1.literalRound571ActualQuantitativeBoundsLevel

g1FiveBlockPhysicalDataLevel : ProofLevel
g1FiveBlockPhysicalDataLevel =
  G1.literalRound571FiveBlockPhysicalDataLevel

------------------------------------------------------------------------
-- H6 shortest nontriviality payment.
------------------------------------------------------------------------

h6SameFamilyWardKernelLevel : ProofLevel
h6SameFamilyWardKernelLevel =
  H6.literalRound563SameFamilyWardKernelSourceLevel

fullOPEStressRequiredBeforeGapOrH6 : Bool
fullOPEStressRequiredBeforeGapOrH6 = false

------------------------------------------------------------------------
-- Global scheduler firewalls.
------------------------------------------------------------------------

arbitraryObservableRepresentationRequired : Bool
arbitraryObservableRepresentationRequired = false

finiteHamiltonianMoscoRouteRequired : Bool
finiteHamiltonianMoscoRouteRequired = false

printedJEqualsWilsonRequired : Bool
printedJEqualsWilsonRequired = false

su2ToGenericPromotionRequired : Bool
su2ToGenericPromotionRequired = false

round578CriticalPathCompilerLevel : ProofLevel
round578CriticalPathCompilerLevel = machineChecked
