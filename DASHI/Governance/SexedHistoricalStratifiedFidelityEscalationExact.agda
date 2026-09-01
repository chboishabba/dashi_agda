module DASHI.Governance.SexedHistoricalStratifiedFidelityEscalationExact where

------------------------------------------------------------------------
-- STRATIFIED TARGETED FIDELITY ESCALATION
--
-- Evidence and model fidelity are orthogonal coordinates.  A consumer may be
-- empirically closed on the live history fibre while the current model remains
-- too coarse to certify the decision at that consumer's stratum.
--
-- This owner reuses the canonical joint information/fidelity policy's
-- `FidelityMove` and `FidelityUnlocksDecision` interfaces, while keeping the
-- Base369 centre/face/edge/corner strata geometric rather than semantic.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

import DASHI.Core.ActionabilityCostedExperimentChoiceExact as Choice
import DASHI.Core.JointSequentialInformationFidelityPolicyExact as Joint
import DASHI.Foundations.Base369Ternary27HypervoxelStratificationExact as Strata
import DASHI.Governance.SexedHistoricalStratifiedMultiConsumerClosureExact as Multi

------------------------------------------------------------------------
-- 1. Stratified fidelity ladder.
------------------------------------------------------------------------

data HistoricalModelFidelity : Set where
  centreFaceFidelity
  edgeFidelity
  cornerFidelity
  : HistoricalModelFidelity

modelCoversStratum : HistoricalModelFidelity → Strata.VoxelStratum → Set
modelCoversStratum centreFaceFidelity Strata.centreStratum = ⊤
modelCoversStratum centreFaceFidelity Strata.faceCentreStratum = ⊤
modelCoversStratum centreFaceFidelity Strata.edgeCentreStratum = ⊥
modelCoversStratum centreFaceFidelity Strata.cornerStratum = ⊥
modelCoversStratum edgeFidelity Strata.centreStratum = ⊤
modelCoversStratum edgeFidelity Strata.faceCentreStratum = ⊤
modelCoversStratum edgeFidelity Strata.edgeCentreStratum = ⊤
modelCoversStratum edgeFidelity Strata.cornerStratum = ⊥
modelCoversStratum cornerFidelity _ = ⊤

DecisionAdequate : HistoricalModelFidelity → Multi.HistoricalConsumer → Set
DecisionAdequate model consumer =
  modelCoversStratum model (Multi.consumerStratum consumer)

centreAdequateAtCoarse :
  DecisionAdequate centreFaceFidelity Multi.reopeningPriorityConsumer
centreAdequateAtCoarse = tt

faceAdequateAtCoarse :
  DecisionAdequate centreFaceFidelity Multi.localOptionConeConsumer
faceAdequateAtCoarse = tt

edgeBlockedAtCoarse :
  DecisionAdequate centreFaceFidelity Multi.globalCompatibilityConsumer → ⊥
edgeBlockedAtCoarse = λ ()

cornerBlockedAtEdge :
  DecisionAdequate edgeFidelity Multi.futureCorridorConsumer → ⊥
cornerBlockedAtEdge = λ ()

------------------------------------------------------------------------
-- 2. Canonical targeted fidelity moves.
------------------------------------------------------------------------

centreFaceToEdge : Joint.FidelityMove HistoricalModelFidelity centreFaceFidelity
centreFaceToEdge =
  Joint.fidelityMove
    (Choice.informationMove
      Choice.increaseFidelity
      1
      "centre/face -> edge historical model fidelity"
      "finite DASHI stratified fidelity fixture"
      "global-compatibility consumer requires edge-level structure")
    refl
    edgeFidelity
    "targeted edge-stratum fidelity escalation"
    "centre/face model does not certify edge consumer"

edgeToCorner : Joint.FidelityMove HistoricalModelFidelity edgeFidelity
edgeToCorner =
  Joint.fidelityMove
    (Choice.informationMove
      Choice.increaseFidelity
      1
      "edge -> corner historical model fidelity"
      "finite DASHI stratified fidelity fixture"
      "future-corridor consumer requires corner-level structure")
    refl
    cornerFidelity
    "targeted corner-stratum fidelity escalation"
    "edge model does not certify corner consumer"

edgeFidelityUnlocksGlobalCompatibility :
  Joint.FidelityUnlocksDecision
    DecisionAdequate
    centreFaceFidelity
    Multi.globalCompatibilityConsumer
edgeFidelityUnlocksGlobalCompatibility =
  Joint.fidelityUnlocksDecision
    centreFaceToEdge
    edgeBlockedAtCoarse
    tt
    "edge fidelity certifies global-compatibility consumer"

cornerFidelityUnlocksFutureCorridor :
  Joint.FidelityUnlocksDecision
    DecisionAdequate
    edgeFidelity
    Multi.futureCorridorConsumer
cornerFidelityUnlocksFutureCorridor =
  Joint.fidelityUnlocksDecision
    edgeToCorner
    cornerBlockedAtEdge
    tt
    "corner fidelity certifies future-corridor consumer"

------------------------------------------------------------------------
-- 3. Target selection is stratum-relative rather than a global model reset.
------------------------------------------------------------------------

data FidelityNeed : Set where
  noEscalationNeeded
  escalateToEdge
  escalateToCorner
  : FidelityNeed

fidelityNeed : HistoricalModelFidelity → Multi.HistoricalConsumer → FidelityNeed
fidelityNeed centreFaceFidelity Multi.reopeningPriorityConsumer = noEscalationNeeded
fidelityNeed centreFaceFidelity Multi.localOptionConeConsumer = noEscalationNeeded
fidelityNeed centreFaceFidelity Multi.globalCompatibilityConsumer = escalateToEdge
fidelityNeed centreFaceFidelity Multi.futureCorridorConsumer = escalateToCorner
fidelityNeed edgeFidelity Multi.futureCorridorConsumer = escalateToCorner
fidelityNeed edgeFidelity _ = noEscalationNeeded
fidelityNeed cornerFidelity _ = noEscalationNeeded

centreConsumerDoesNotEscalateAtCoarse :
  fidelityNeed centreFaceFidelity Multi.reopeningPriorityConsumer
  ≡ noEscalationNeeded
centreConsumerDoesNotEscalateAtCoarse = refl

edgeConsumerRequestsEdgeOnly :
  fidelityNeed centreFaceFidelity Multi.globalCompatibilityConsumer
  ≡ escalateToEdge
edgeConsumerRequestsEdgeOnly = refl

cornerConsumerRequestsCorner :
  fidelityNeed centreFaceFidelity Multi.futureCorridorConsumer
  ≡ escalateToCorner
cornerConsumerRequestsCorner = refl

------------------------------------------------------------------------
-- 4. Fidelity escalation preserves the already adequate lower-stratum model
-- obligations in this finite ladder.
------------------------------------------------------------------------

edgeStillCoversCentre : DecisionAdequate edgeFidelity Multi.reopeningPriorityConsumer
edgeStillCoversCentre = tt

edgeStillCoversFace : DecisionAdequate edgeFidelity Multi.localOptionConeConsumer
edgeStillCoversFace = tt

cornerStillCoversEdge : DecisionAdequate cornerFidelity Multi.globalCompatibilityConsumer
cornerStillCoversEdge = tt

------------------------------------------------------------------------
-- 5. Evidence/fidelity boundary is inherited from the canonical joint policy.
------------------------------------------------------------------------

canonicalJointPolicyBoundaryStillApplies : Joint.JointSequentialPolicyBoundary
canonicalJointPolicyBoundaryStillApplies = Joint.canonicalJointSequentialPolicyBoundary

------------------------------------------------------------------------
-- 6. No-promotion boundaries.
------------------------------------------------------------------------

data FidelityMoveCreatesNewHistoricalEvidence : Set where

data HighStratumNeedForcesGlobalReset : Set where

data HigherFidelityMeansHistoricallyTruer : Set where

data StratumOrderIsMoralHierarchy : Set where

data CornerConsumerIsIntrinsicallyMoreImportant : Set where

data EvidenceClosureImpliesModelAdequacy : Set where

data ModelAdequacyImpliesAuthority : Set where

fidelityMoveDoesNotCreateNewHistoricalEvidence :
  FidelityMoveCreatesNewHistoricalEvidence → ⊥
fidelityMoveDoesNotCreateNewHistoricalEvidence ()

highStratumNeedDoesNotForceGlobalReset :
  HighStratumNeedForcesGlobalReset → ⊥
highStratumNeedDoesNotForceGlobalReset ()

higherFidelityDoesNotMeanHistoricallyTruer :
  HigherFidelityMeansHistoricallyTruer → ⊥
higherFidelityDoesNotMeanHistoricallyTruer ()

stratumOrderIsNotMoralHierarchy : StratumOrderIsMoralHierarchy → ⊥
stratumOrderIsNotMoralHierarchy ()

cornerConsumerIsNotIntrinsicallyMoreImportant :
  CornerConsumerIsIntrinsicallyMoreImportant → ⊥
cornerConsumerIsNotIntrinsicallyMoreImportant ()

evidenceClosureDoesNotImplyModelAdequacy :
  EvidenceClosureImpliesModelAdequacy → ⊥
evidenceClosureDoesNotImplyModelAdequacy ()

modelAdequacyDoesNotCreateAuthority : ModelAdequacyImpliesAuthority → ⊥
modelAdequacyDoesNotCreateAuthority ()

record StratifiedFidelityEscalationBoundary : Set where
  constructor stratified-fidelity-escalation-boundary
  field
    fidelityIsStratumIndexed : Bool
    centreAndFaceCanCloseAtCoarseFidelity : Bool
    edgeCanRequireTargetedEscalation : Bool
    cornerCanRequireFurtherEscalation : Bool
    higherFidelityPreservesLowerCoverageInFixture : Bool
    fidelityMoveCreatesHistoricalEvidence : Bool
    highStratumNeedForcesGlobalReset : Bool
    stratumOrderIsMoralHierarchy : Bool
    modelAdequacyCreatesAuthority : Bool

canonicalStratifiedFidelityEscalationBoundary :
  StratifiedFidelityEscalationBoundary
canonicalStratifiedFidelityEscalationBoundary =
  stratified-fidelity-escalation-boundary
    true true true true true false false false false
