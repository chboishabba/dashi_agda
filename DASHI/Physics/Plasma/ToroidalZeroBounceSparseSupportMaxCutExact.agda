module DASHI.Physics.Plasma.ToroidalZeroBounceSparseSupportMaxCutExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Physics.Plasma.ToroidalZeroBounceSparseSupportExact as Sparse
import DASHI.Physics.Plasma.ToroidalZeroBounceSupportPatchHyperfabricExact as Patch
import DASHI.Physics.Plasma.ToroidalZeroBounceTernary27MaxCutExact as Prior
import DASHI.Physics.Plasma.ZeroBouncePopulationExact as ZeroBounce

------------------------------------------------------------------------
-- SPARSE-SUPPORT MAX-CUT
--
-- Geometry-stage local replay currently finds:
--   * one dominant mode alone is consumer-inadequate under the declared replay;
--   * a two-mode support survives the coarse geometry-retention consumer;
--   * a three-mode support reproduces the present full-chart optimum to the
--     numerical precision of the replay.
--
-- These are numerical receipts only.  Full orbit / coil / kinetic consumers
-- may reopen support.  The owner therefore records the search compression and
-- refuses to promote sparse geometry into a final physical architecture.
------------------------------------------------------------------------

record SparseSupportMaxCut
    (population : ZeroBounce.DeclaredParticlePopulation) : Set₁ where
  constructor sparse-support-max-cut
  field
    priorTernary27Cut : Prior.Ternary27SearchMaxCut population
    supportHyperformal : Patch.SupportPatchHyperformal population
    oneModeGeometryCounterexampleReceipt : Set
    twoModeGeometryRetentionReceipt : Set
    threeModeFullChartReplayReceipt : Set
    hardPhysicsPrecedesSupportMDLReceipt : Set
    orbitConsumerMayReopenSupportReceipt : Set
    coilInverseConsumerMayReopenSupportReceipt : Set
    kineticStabilityMayReopenSupportReceipt : Set
    bestKnownReferenceMayReopenSupportReceipt : Set
    maxCutReference : String

open SparseSupportMaxCut public

record SparseSupportMaxCutBoundary : Set where
  constructor sparse-support-max-cut-boundary
  field
    localTwoModeReceiptProvesFinalReactorArchitecture : Bool
    localTwoModeReceiptProvesFinalReactorArchitectureIsFalse :
      localTwoModeReceiptProvesFinalReactorArchitecture ≡ false

    localThreeModeReplayIsKernelTheorem : Bool
    localThreeModeReplayIsKernelTheoremIsFalse :
      localThreeModeReplayIsKernelTheorem ≡ false

    supportCompressionBeforeCoilAndOrbitSolveIsUseful : Bool
    supportCompressionBeforeCoilAndOrbitSolveIsUsefulIsTrue :
      supportCompressionBeforeCoilAndOrbitSolveIsUseful ≡ true

    downstreamCounterexampleMayReopenSupport : Bool
    downstreamCounterexampleMayReopenSupportIsTrue :
      downstreamCounterexampleMayReopenSupport ≡ true

canonicalSparseSupportMaxCutBoundary : SparseSupportMaxCutBoundary
canonicalSparseSupportMaxCutBoundary =
  sparse-support-max-cut-boundary
    false refl
    false refl
    true refl
    true refl

localReplayReference : String
localReplayReference =
  "2026-10-07 local Python replay: 24 free coordinates; geometry consumer rejects k=1; accepts k=2 within declared 5 percent objective / B / curvature tolerances; k=3 reproduces current full-chart geometry optimum. scripts/ternary27_sparse_support.py"
