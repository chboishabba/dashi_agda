{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.YangMillsClayCriticalPathRound561Exact where

------------------------------------------------------------------------
-- GOAL-1 / ROUND561:
-- POST-R559/R560 SEVEN-FAMILY CLAY CRITICAL PATH
--
-- R558 still labelled T5 as a "same-family" attachment.  R559 removes that
-- architecture: the exponential-moment producer is constructed directly on the
-- literal CMP119 finite expectation sequence, and R560 compiles it into the
-- canonical OS0/OS5 limit data.
--
-- The critical families remain seven, but their proof shapes are now:
--
--   A3  selected cylinder/Wilson continuum representation;
--   T1  concrete finite/RG + published finite OS source;
--   T5  literal CMP119 exponential-moment source (NO family weld);
--   B1  source-first Wilson WEXT on the exact selected covariance carrier;
--   B2  same reconstructed-H transfer coordinate;
--   G1  actual compact-simple + quantitative/five-block source;
--   H6  minimal same-family Gaussian/Ward kernel.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false)
open import Agda.Builtin.Nat using (Nat)

open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Physics.YangMills.YangMillsClayPostSelectedCylinderFrontierRound548Exact as A3
import DASHI.Physics.YangMills.YangMillsConcreteT1FiniteOSSourceRound545Exact as T1
import DASHI.Physics.YangMills.YangMillsLiteralCMP119QuantitativeMomentsRound559Exact as T5
import DASHI.Physics.YangMills.YangMillsLiteralCMP119OS05FromMomentsRound560Exact as OS05
import DASHI.Physics.YangMills.YangMillsSourceFirstWilsonCovarianceRound556Exact as B1
import DASHI.Physics.YangMills.YangMillsSourceFirstWilsonMassGapRound557Exact as BGap
import DASHI.Physics.YangMills.BalabanWilsonWEXTMaxCutRound494Exact as WEXT
import DASHI.Physics.YangMills.YangMillsActualGroupCompleteSourceRound543Exact as G1
import DASHI.Physics.YangMills.YangMillsClayMinimalH6NontrivialityRound550Exact as H6
import DASHI.Physics.YangMills.YangMillsClayCPhysicalPackageMaxCutRound527Exact as C

data CriticalFamily : Set where
  a3SelectedRepresentation : CriticalFamily
  t1FiniteOSSameFamily : CriticalFamily
  t5LiteralCMP119Moments : CriticalFamily
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
criticalLevel t5LiteralCMP119Moments =
  T5.literalRound559CMP119ExponentialMomentProducerLevel
criticalLevel b1SourceFirstWilsonWEXT =
  B1.literalRound556SourceFirstWilsonCarrierLevel
criticalLevel b2SameHamiltonian =
  BGap.literalRound557SameHamiltonianTransferLevel
criticalLevel g1ActualCompactSimple =
  G1.literalRound543ActualGroupCompleteSourceLevel
criticalLevel h6MinimalWardNontriviality =
  H6.literalRound550MinimalWardKernelLevel

------------------------------------------------------------------------
-- Critical compilers/subclaims kept visible.
------------------------------------------------------------------------

t5FiniteOS05CompilerLevel : ProofLevel
t5FiniteOS05CompilerLevel =
  OS05.round560FiniteOS05FromLiteralMomentsLevel

t5CanonicalClosureAuthorityLevel : ProofLevel
t5CanonicalClosureAuthorityLevel =
  OS05.round560CanonicalClosureAuthorityLevel

t5SameFamilyExpectationAttachmentRequired : Bool
t5SameFamilyExpectationAttachmentRequired =
  T5.round559SameFiniteExpectationAttachmentRequired

finiteToContinuumWilsonCovarianceLevel : ProofLevel
finiteToContinuumWilsonCovarianceLevel =
  BGap.round557FiniteToContinuumCovarianceCompilerLevel

massGapCompilerLevel : ProofLevel
massGapCompilerLevel =
  BGap.round557MassGapCompilerLevel

wextTwoMarkExpansionLevel : ProofLevel
wextTwoMarkExpansionLevel =
  WEXT.literalRound494WilsonTwoMarkExpansionLevel

wextConnectingWeightTailLevel : ProofLevel
wextConnectingWeightTailLevel =
  WEXT.literalRound494WilsonConnectingWeightTailLevel

a3CylinderGeneratorRepresentationLevel : ProofLevel
a3CylinderGeneratorRepresentationLevel =
  A3.a3CylinderGeneratorRepresentationLevel

minimalH6CompilerLevel : ProofLevel
minimalH6CompilerLevel =
  H6.round550MinimalH6CompilerLevel

------------------------------------------------------------------------
-- Conservative Clay local-field finish remains outside the gap cut.
------------------------------------------------------------------------

fullCLayerRequiredForMassGap : Bool
fullCLayerRequiredForMassGap = false

fullCLayerRequiredForMinimalH6 : Bool
fullCLayerRequiredForMinimalH6 = false

fullCLayerRetainedForConservativeClayExistence : Bool
fullCLayerRetainedForConservativeClayExistence = true

printedJRouteRequired : Bool
printedJRouteRequired = false

finiteHamiltonianMoscoRouteRequired : Bool
finiteHamiltonianMoscoRouteRequired = false

round561CriticalPathCompilerLevel : ProofLevel
round561CriticalPathCompilerLevel = machineChecked
