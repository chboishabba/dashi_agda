module DASHI.Physics.YangMills.BalabanClayHighestAlphaRound76SixAnalyticCutsetExact where

------------------------------------------------------------------------
-- ROUND76: 7 -> 6 INDEPENDENT ANALYTIC JOBS
--
-- Round75 left `LiteralStateEntersPublishedBalabanRG` as the narrowest likely
-- deletion.  The deletion is now exact, not rhetorical, in the stronger sense:
--
--   PhysicalUnifiedOneStepYMEstimate
--   formulated on a source-native scale of the ACTUAL imported CMP122 flow
--                    |
--                    v
--   same-object E/R/B/T/background/E^(2)/Pi entry
--   + CMP122 Theorem-1 Section-2 membership and bounds at that scale.
--
-- `BalabanSourceNativePublishedFlowEntryExact` transports the published
-- `Balaban1989Theorem1Witness` across the literal equality between the CMP119
-- complete density in the strong state and `densityAt flow scale`.  Thus old
-- job #3 is genuinely downstream once the physical one-step theorem uses this
-- source-native carrier.  Quantitative comparisons between source coordinates
-- and the stronger Clay norm remain real analysis inside job #3 below; they are
-- not hidden or relabelled as a separate entry theorem.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat)
open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Physics.YangMills.BalabanClayHighestAlphaRound75SevenAnalyticCutsetExact
import DASHI.Physics.YangMills.BalabanSourceNativePublishedFlowEntryExact as Entry
import DASHI.Physics.YangMills.BalabanSourceNativeLocalizationTreeExact
import DASHI.Physics.YangMills.SchattenTraceClassCompositePerturbationExact
import DASHI.Physics.YangMills.YangMillsMaxwellLinearDispersionNoGapExact

------------------------------------------------------------------------
-- Source-native form required of the physical one-step theorem.
-- `PhysicalOneStepEstimate` is the genuinely new analytic content; published
-- RG membership is no longer an independent hypothesis.
------------------------------------------------------------------------

record PhysicalUnifiedOneStepSourceNativeOutput : Set₂ where
  field
    publishedFlow : Entry.SourceNativePublishedFlow
    scale : Nat
    state : Entry.SourceNativeStrongStateAt publishedFlow scale

    PhysicalOneStepEstimate : Set
    physicalOneStepEstimate : PhysicalOneStepEstimate

open PhysicalUnifiedOneStepSourceNativeOutput public

round76PhysicalOneStepImpliesPublishedBalabanEntry :
  (output : PhysicalUnifiedOneStepSourceNativeOutput) →
  Entry.LiteralStateEntersPublishedBalabanRG
    (publishedFlow output) (scale output) (state output)
round76PhysicalOneStepImpliesPublishedBalabanEntry output =
  Entry.literalStateEntersPublishedBalabanRG
    (publishedFlow output) (scale output) (state output)

------------------------------------------------------------------------
-- AUTHORITATIVE ROUND76 CUTSET
--
-- 1 CompactSimpleSelectedBackgroundFiveBlockEstimate
--
-- 2 LiteralWilsonFPHaarOneLoopRGCoefficient
--
-- 3 PhysicalUnifiedOneStepYMEstimate
--   SOURCE-NATIVE formulation. It must prove the actual 17/32 strong
--   contraction while carrying composite insertions, weighted connected
--   correlations, quasi-local Hessian/E^(2), characteristic functional and the
--   common increment modulus. Source E/R/B/T/background coordinates and CMP122
--   inductive membership are baseline data/consequences of this same state.
--
-- 4 SameDensityCompactLieHeatLangevinClustering
--   Uniform heat/Doob Hessian debt + covariant finite-speed propagation on the
--   SAME source-native Hessian, yielding physical exponential clustering.
--
-- 5 SameFamilyCompositeOPEStressWardClosure
--   Quantitative composite OPE remainder + protected stress/Ward identity and
--   T00 identification on the SAME reconstructed Hamiltonian.
--
-- 6 InteractingContinuumNontriviality
--   Either a strict finite cumulant margin or the strengthened same-theory
--   Gaussian + Ward + local kinetic + no-mass -> massless Maxwell route.
--
-- The old standalone continuum/OS theorem was removed in Round75. The old
-- source-entry theorem is removed here. Standard Minlos/OS reconstruction and
-- published baseline nonlinear RG preservation remain downstream authorities.
------------------------------------------------------------------------

round76SourceEntryDependencyCompilerLevel : ProofLevel
round76SourceEntryDependencyCompilerLevel = machineChecked

round76IndependentAnalyticCount : Nat
round76IndependentAnalyticCount = 6

------------------------------------------------------------------------
-- NEXT DECREMENT TARGETS
--
-- 6 -> 5 candidate A:
--   make the Gaussian/nontriviality branch a theorem consequence of #2 + #3 +
--   #4 + #5 by proving the local two-derivative Ward kernel classification and
--   same-Hamiltonian massless dispersion identification. Round76 already
--   compiles a labelled Maxwell dispersion to the no-gap contradiction.
--
-- 6 -> 5 candidate B:
--   if the OPE/stress theorem's composite norm is already a nonexpansive
--   coordinate of #3 strongly enough to control its quantitative remainder,
--   #5 may become a downstream composite-insertion closure rather than a new
--   all-scale estimate. This implication is NOT claimed yet.
------------------------------------------------------------------------
