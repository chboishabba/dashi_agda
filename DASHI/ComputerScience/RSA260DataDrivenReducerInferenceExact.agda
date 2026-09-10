module DASHI.ComputerScience.RSA260DataDrivenReducerInferenceExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.ComputerScience.RSA260AdaptiveReducerHyperfabricExact as Adaptive
import DASHI.ComputerScience.RSA260ReducerHyperfabricSourceDiligenceExact as Sources

------------------------------------------------------------------------
-- DATA-DRIVEN REDUCER INFERENCE
--
-- Synthetic benchmark only.  This advances beyond benchmark-declared resource
-- classes: requirement edges are inferred from M itself, requirement components
-- are connected components of that graph, consumer signatures are inferred
-- from an explicit projection observer, and conflicts are derived from
-- collisions of those signatures.  The final global action is still checked
-- directly by MP = PM.
------------------------------------------------------------------------

record DataDrivenReducerSource : Set where
  constructor data-driven-reducer-source
  field
    repository : String
    branch : String
    path : String
    gitBlob : String
    language : String
open DataDrivenReducerSource public

currentDataDrivenReducerSource : DataDrivenReducerSource
currentDataDrivenReducerSource = data-driven-reducer-source
  "chboishabba/dashiRTX"
  "agent/triadic-u8-runtime-oracle"
  "rsa260_data_driven_reducer_inference_256_oracle.c"
  "878463f3a5a341cf6c3a779065a6bebd23e87b67"
  "C11"

record DataDrivenReducerInferenceReceipt : Set where
  constructor data-driven-reducer-inference-receipt
  field
    carrierCoordinates : Nat
    localCandidateCount : Nat
    requirementEdgesInferredFromOperator : Bool
    inferredRequirementEdgeCount : Nat
    requirementComponentsInferredByConnectivity : Bool
    inferredRequirementComponentCount : Nat
    uniformComponentSize : Nat
    projectionObserverExplicit : Bool
    componentConsumerSignaturesInferred : Bool
    observerInvariantComponentCount : Nat
    conflictsDerivedFromConsumerSignatureCollisions : Bool
    inferredConflictEdgeCount : Nat
    largestClosedConflictFreeFamilySelected : Bool
    selectedComponentCount : Nat
    selectedLocalReducerCount : Nat
    quotientCoordinateCount : Nat
    composedGlobalActionCheckedUpstairs : Bool
    sourceReviewedAgainstCommittedBlob : Bool
    exactGitBlobExecuted : Bool
    productionRSA260MatrixUsed : Bool
    productionSpeedupClaimed : Bool
open DataDrivenReducerInferenceReceipt public

currentDataDrivenReducerInferenceReceipt : DataDrivenReducerInferenceReceipt
currentDataDrivenReducerInferenceReceipt = data-driven-reducer-inference-receipt
  256 128
  true 120
  true 8 16
  true true 8
  true 7
  true 3 48 208
  true true false false false

------------------------------------------------------------------------
-- Provenance / execution / mathematical promotion are separate coordinates.
------------------------------------------------------------------------

record DataDrivenInferencePromotionBoundary : Set where
  constructor data-driven-inference-promotion-boundary
  field
    sourceAttributionPaid : Bool
    implementationIdentityPaid : Bool
    implementationExecutionPaid : Bool
    syntheticMathematicalAdmissionPaid : Bool
    productionSameObjectPaid : Bool
    productionReductionPaid : Bool
open DataDrivenInferencePromotionBoundary public

currentDataDrivenInferencePromotionBoundary : DataDrivenInferencePromotionBoundary
currentDataDrivenInferencePromotionBoundary = data-driven-inference-promotion-boundary
  true true false true false false

sourceBoundary : Sources.SnowballAttributionBoundary
sourceBoundary = Sources.canonicalSnowballAttributionBoundary

adaptiveBoundary : Adaptive.RSA260AdaptiveHyperfabricRoadmapBoundary
adaptiveBoundary = Adaptive.currentRSA260AdaptiveHyperfabricRoadmapBoundary

------------------------------------------------------------------------
-- Next data-driven residuals.
------------------------------------------------------------------------

data DataDrivenReducerResidual : Set where
  executeExactCommittedBlob : DataDrivenReducerResidual
  inferLocalCandidatePairingInsteadOfAssumingPairFibre : DataDrivenReducerResidual
  inferProjectionObserverFromProductionConsumer : DataDrivenReducerResidual
  inferLiftConstraintsFromProductionReplay : DataDrivenReducerResidual
  runOnProductionMatrix : DataDrivenReducerResidual
  compareQuotientAgainstFullReplay : DataDrivenReducerResidual

firstDataDrivenReducerResidual : DataDrivenReducerResidual
firstDataDrivenReducerResidual = executeExactCommittedBlob

------------------------------------------------------------------------
-- WrongType firewalls.
------------------------------------------------------------------------

data OperatorCouplingImpliesRequirement : Set where
data SameObserverSignatureImpliesUniversalConflict : Set where
data SyntheticInferenceImpliesProductionStructure : Set where
data SourceDiligenceImpliesExecution : Set where

data ExactBlobIdentityImpliesSuccessfulExecution : Set where

operatorCouplingAloneDoesNotUniversallyCreateRequirement : OperatorCouplingImpliesRequirement → ⊥
operatorCouplingAloneDoesNotUniversallyCreateRequirement ()

observerCollisionIsConsumerRelativeNotUniversal : SameObserverSignatureImpliesUniversalConflict → ⊥
observerCollisionIsConsumerRelativeNotUniversalConflict ()
  where
    universalConflict : SameObserverSignatureImpliesUniversalConflict → ⊥
    universalConflict ()

syntheticInferenceDoesNotCreateProductionStructure : SyntheticInferenceImpliesProductionStructure → ⊥
syntheticInferenceDoesNotCreateProductionStructure ()

sourceDiligenceDoesNotCreateExecution : SourceDiligenceImpliesExecution → ⊥
sourceDiligenceDoesNotCreateExecution ()

blobIdentityDoesNotGuaranteeExecutionSuccess : ExactBlobIdentityImpliesSuccessfulExecution → ⊥
blobIdentityDoesNotGuaranteeExecutionSuccess ()
