module DASHI.ComputerScience.RSA260AdaptiveHyperfabricProductionRoadmapExact where

open import DASHI.Core.Prelude
open import Data.Empty using (⊥)

import DASHI.ComputerScience.RSA260NDimSymmetryProductionRoadmapExact as Prior
import DASHI.ComputerScience.RSA260FractalPadicHyperfabricBatchGluingExact as Gluing
import DASHI.ComputerScience.RSA260AdaptiveReducerHyperfabricExact as Adaptive

------------------------------------------------------------------------
-- CONSOLIDATED ROADMAP AFTER ADAPTIVE HYPERFABRIC BATCH SELECTION
--
-- Conclusion payment remains acquisition-first.  The middle replay-preparation
-- lane is now refined into recursive coordinate discrimination plus a typed
-- reducer hyperfabric with must-not-compose and must-compose relations.
------------------------------------------------------------------------

priorRoadmap : Prior.ConsolidatedRSA260RoadmapBoundary
priorRoadmap = Prior.currentConsolidatedRSA260RoadmapBoundary

gluingRoadmap : Gluing.HierarchicalBatchRoadmapBoundary
gluingRoadmap = Gluing.currentHierarchicalBatchRoadmapBoundary

adaptiveRoadmap : Adaptive.RSA260AdaptiveHyperfabricRoadmapBoundary
adaptiveRoadmap = Adaptive.currentRSA260AdaptiveHyperfabricRoadmapBoundary

data AdaptiveProductionResidual : Set where
  acquireProductionLAInput : AdaptiveProductionResidual
  verifySameObjectManifest : AdaptiveProductionResidual
  coarseCoordinateRefinement : AdaptiveProductionResidual
  descendAmbiguousFibres : AdaptiveProductionResidual
  enumerateLocalReducers : AdaptiveProductionResidual
  classifyConflictEdges : AdaptiveProductionResidual
  classifyCoRequirementEdges : AdaptiveProductionResidual
  closeRequirementComponents : AdaptiveProductionResidual
  selectConflictFreeClosedBatch : AdaptiveProductionResidual
  composeGlobalCandidateAction : AdaptiveProductionResidual
  verifyOperatorAndConsumerEquivariance : AdaptiveProductionResidual
  chooseQuotientOrFullWidthReplay : AdaptiveProductionResidual
  replayCPU : AdaptiveProductionResidual
  liftAndVerifyUpstairs : AdaptiveProductionResidual
  reproduceCUDA : AdaptiveProductionResidual
  reproduceNCCL : AdaptiveProductionResidual
  reproduceRemainingGNFS : AdaptiveProductionResidual
  closeEndToEndRSA260 : AdaptiveProductionResidual

firstUnpaidAdaptiveProductionResidual : AdaptiveProductionResidual
firstUnpaidAdaptiveProductionResidual = acquireProductionLAInput

record AdaptiveHyperfabricProductionBoundary : Set where
  constructor adaptive-hyperfabric-production-boundary
  field
    syntheticBlockWiedemannPaid : Bool
    syntheticGraphRefinementPaid : Bool
    syntheticOneComponentGluingClosurePaid : Bool
    syntheticMultiComponentConflictSelectionRepresented : Bool
    recursivePadicRefinementPolicyRepresented : Bool
    conflictVsCoRequirementDistinctionRepresented : Bool
    largestClosedBatchSelectionRepresented : Bool
    selectedBatchEquivarianceRepresented : Bool
    productionBytesPaid : Bool
    productionRecursiveRefinementPaid : Bool
    productionReducerHyperfabricPaid : Bool
    productionQuotientDecisionPaid : Bool
    productionCPUReplayPaid : Bool
    productionLiftPaid : Bool
    productionCUDAParityPaid : Bool
    productionNCCLParityPaid : Bool
    fullRSA260ReproductionPaid : Bool
open AdaptiveHyperfabricProductionBoundary public

currentAdaptiveHyperfabricProductionBoundary : AdaptiveHyperfabricProductionBoundary
currentAdaptiveHyperfabricProductionBoundary =
  adaptive-hyperfabric-production-boundary
    true true true true true true true true
    false false false false false false false false false

------------------------------------------------------------------------
-- Operational order after bytes arrive.
--
-- A recursive dimension is admitted only while it changes a consumer-relevant
-- partition or reducer relation.  Requirement closure happens before batch
-- optimisation.  Conflict-free selection happens before global equivariance.
-- Failure anywhere falls back to full-width CPU replay rather than blocking
-- correctness.
------------------------------------------------------------------------

record AdaptiveReplayPolicy : Set where
  constructor adaptive-replay-policy
  field
    addAxisOnlyOnObservedGain : Bool
    closeRequirementsBeforeOptimisingBatch : Bool
    rejectBatchesContainingConflict : Bool
    requireGlobalMPEqualsPM : Bool
    failedSymmetrySearchFallsBackToFullWidth : Bool
    quotientReplayEliminatesUpstairsVerification : Bool
open AdaptiveReplayPolicy public

canonicalAdaptiveReplayPolicy : AdaptiveReplayPolicy
canonicalAdaptiveReplayPolicy = adaptive-replay-policy
  true true true true true false

------------------------------------------------------------------------
-- WrongType firewalls.
------------------------------------------------------------------------

data MoreRecursiveDepthImpliesMoreReduction : Set where
data RequirementClosureImpliesAdmissibleBatch : Set where
data LargestClosedBatchImpliesEquivariance : Set where
data SyntheticHyperformImpliesProductionHyperform : Set where

moreDepthDoesNotGuaranteeReduction : MoreRecursiveDepthImpliesMoreReduction → ⊥
moreDepthDoesNotGuaranteeReduction ()

closureDoesNotGuaranteeAdmissibility : RequirementClosureImpliesAdmissibleBatch → ⊥
closureDoesNotGuaranteeAdmissibility ()

largestClosedBatchDoesNotCreateEquivariance : LargestClosedBatchImpliesEquivariance → ⊥
largestClosedBatchDoesNotCreateEquivariance ()

syntheticHyperformDoesNotCreateProductionHyperform :
  SyntheticHyperformImpliesProductionHyperform → ⊥
syntheticHyperformDoesNotCreateProductionHyperform ()
