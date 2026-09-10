module DASHI.ComputerScience.RSA260AdaptiveHyperfabricProductionRoadmapExact where

open import DASHI.Core.Prelude
open import Data.Empty using (⊥)

import DASHI.ComputerScience.RSA260NDimSymmetryProductionRoadmapExact as Prior
import DASHI.ComputerScience.RSA260FractalPadicHyperfabricBatchGluingExact as Gluing
import DASHI.ComputerScience.RSA260AdaptiveReducerHyperfabricExact as Adaptive
import DASHI.ComputerScience.RSA260DataDrivenReducerInferenceExact as DataDriven
import DASHI.ComputerScience.RSA260ReducerHyperfabricSourceDiligenceExact as Sources

------------------------------------------------------------------------
-- CONSOLIDATED ROADMAP AFTER DATA-DRIVEN ADAPTIVE HYPERFABRIC INFERENCE
--
-- Conclusion payment remains acquisition-first.  The middle replay-preparation
-- lane now distinguishes:
--   declared synthetic benchmark structure,
--   inferred synthetic reducer structure,
--   exact executable receipt,
--   production same-object application.
------------------------------------------------------------------------

priorRoadmap : Prior.ConsolidatedRSA260RoadmapBoundary
priorRoadmap = Prior.currentConsolidatedRSA260RoadmapBoundary

gluingRoadmap : Gluing.HierarchicalBatchRoadmapBoundary
gluingRoadmap = Gluing.currentHierarchicalBatchRoadmapBoundary

adaptiveRoadmap : Adaptive.RSA260AdaptiveHyperfabricRoadmapBoundary
adaptiveRoadmap = Adaptive.currentRSA260AdaptiveHyperfabricRoadmapBoundary

dataDrivenBoundary : DataDriven.DataDrivenInferencePromotionBoundary
dataDrivenBoundary = DataDriven.currentDataDrivenInferencePromotionBoundary

sourceBoundary : Sources.SnowballAttributionBoundary
sourceBoundary = Sources.canonicalSnowballAttributionBoundary

data AdaptiveProductionResidual : Set where
  acquireProductionLAInput : AdaptiveProductionResidual
  verifySameObjectManifest : AdaptiveProductionResidual
  coarseCoordinateRefinement : AdaptiveProductionResidual
  descendAmbiguousFibres : AdaptiveProductionResidual
  inferLocalReducerCandidates : AdaptiveProductionResidual
  inferCoRequirementEdgesFromOperator : AdaptiveProductionResidual
  closeRequirementComponents : AdaptiveProductionResidual
  inferConsumerSignatures : AdaptiveProductionResidual
  inferConflictEdgesFromConsumer : AdaptiveProductionResidual
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
    sourceDiligencePolicyAttached : Bool
    primaryColouringSourceAttributed : Bool
    conceptQIDsRecordedWithoutPromotion : Bool
    irrelevantOEISIdentifierRejected : Bool
    operatorDerivedRequirementInferenceImplemented : Bool
    observerDerivedConflictInferenceImplemented : Bool
    dataDrivenClosedBatchSelectionImplemented : Bool
    exactDataDrivenRuntimeBlobExecutionPaid : Bool
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
    true true true true
    true true true false
    false false false false false false false false false

------------------------------------------------------------------------
-- Operational order after bytes arrive.
--
-- A recursive dimension is admitted only while it changes a consumer-relevant
-- partition or reducer relation.  Requirement inference/closure happens before
-- consumer-relative conflict inference and batch optimisation.  Failure of the
-- optional reduction path falls back to full-width CPU replay.
------------------------------------------------------------------------

record AdaptiveReplayPolicy : Set where
  constructor adaptive-replay-policy
  field
    addAxisOnlyOnObservedGain : Bool
    inferRequirementsBeforeOptimisingBatch : Bool
    closeRequirementsBeforeInferringClosedComponentConflicts : Bool
    conflictsRemainConsumerRelative : Bool
    rejectBatchesContainingConflict : Bool
    requireGlobalMPEqualsPM : Bool
    requireObserverCovariance : Bool
    failedSymmetrySearchFallsBackToFullWidth : Bool
    quotientReplayEliminatesUpstairsVerification : Bool
open AdaptiveReplayPolicy public

canonicalAdaptiveReplayPolicy : AdaptiveReplayPolicy
canonicalAdaptiveReplayPolicy = adaptive-replay-policy
  true true true true true true true true false

------------------------------------------------------------------------
-- Snowball/source order is orthogonal to mathematical dependency order.
------------------------------------------------------------------------

record RoadmapSourcePaymentBoundary : Set where
  constructor roadmap-source-payment-boundary
  field
    sourceAcquisitionMaySnowballOutOfOrder : Bool
    conclusionPaymentMaySnowballOutOfOrder : Bool
    DOIAlonePaysTheorem : Bool
    QIDAlonePaysConceptApplicability : Bool
    OEISRequiredWhenNoSequenceClaimExists : Bool
    implementationIdentityPaysExecution : Bool
open RoadmapSourcePaymentBoundary public

canonicalRoadmapSourcePaymentBoundary : RoadmapSourcePaymentBoundary
canonicalRoadmapSourcePaymentBoundary = roadmap-source-payment-boundary
  true false false false false false

------------------------------------------------------------------------
-- WrongType firewalls.
------------------------------------------------------------------------

data MoreRecursiveDepthImpliesMoreReduction : Set where
data RequirementClosureImpliesAdmissibleBatch : Set where
data LargestClosedBatchImpliesEquivariance : Set where
data SyntheticHyperformImpliesProductionHyperform : Set where
data SourceIdentityImpliesExecution : Set where

moreDepthDoesNotGuaranteeReduction : MoreRecursiveDepthImpliesMoreReduction → ⊥
moreDepthDoesNotGuaranteeReduction ()

closureDoesNotGuaranteeAdmissibility : RequirementClosureImpliesAdmissibleBatch → ⊥
closureDoesNotGuaranteeAdmissibility ()

largestClosedBatchDoesNotCreateEquivariance : LargestClosedBatchImpliesEquivariance → ⊥
largestClosedBatchDoesNotCreateEquivariance ()

syntheticHyperformDoesNotCreateProductionHyperform :
  SyntheticHyperformImpliesProductionHyperform → ⊥
syntheticHyperformDoesNotCreateProductionHyperform ()

sourceIdentityDoesNotCreateExecution : SourceIdentityImpliesExecution → ⊥
sourceIdentityDoesNotCreateExecution ()
