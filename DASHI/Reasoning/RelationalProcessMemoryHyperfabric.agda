module DASHI.Reasoning.RelationalProcessMemoryHyperfabric where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Cognition.PNF.EventAlgebra as PNF
import DASHI.Reasoning.TypedHyperfabricCore as Hyperfabric
import DASHI.Reasoning.RelationalStateCore as Core
import DASHI.Reasoning.ConditionalResponseTree as Response

------------------------------------------------------------------------
-- Process-bearing branches.
--
-- An unrealised outcome may still carry accumulated search state, provenance,
-- expiring opportunities, external dependencies and transfer obligations.
------------------------------------------------------------------------

data BranchKind : Set where
  purePossibility deliberativeBranch goalProcessBranch : BranchKind

data OutcomeStatus : Set where
  outcomeAbsent outcomePartial outcomeAchieved outcomeFailed : OutcomeStatus

data LivenessLayer : Set where
  logicalLiveness institutionalLiveness economicLiveness : LivenessLayer
  agentLiveness capacityLiveness temporalLiveness : LivenessLayer

data BranchStatus : Set where
  unstarted searching pending blocked expiredUnselected : BranchStatus
  handoverPending abandoned failed selected executed : BranchStatus

data InertiaKind : Set where
  effectInertia processInertia searchInertia handoverInertia : InertiaKind
  switchingInertia windowInertia capacityInertia : InertiaKind

data AttractorAlignment : Set where
  alignedWithAttractor orthogonalToAttractor opposedToAttractor : AttractorAlignment
  unknownAlignment : AttractorAlignment

data PhaseRelation : Set where
  inPhase quadraturePhase oppositePhase incoherentPhase : PhaseRelation

data InterferenceKind : Set where
  constructiveInterference neutralInterference destructiveInterference : InterferenceKind
  undeterminedInterference : InterferenceKind

record SearchState : Set where
  constructor searchState
  field
    activeApplications : List String
    documents : List String
    contacts : List String
    queuePositions : List String
    learnedConstraints : List String
    pendingResponses : List String
    stateReceipt : String

open SearchState public

record LivenessWitness : Set where
  constructor livenessWitness
  field
    layer : LivenessLayer
    live : Bool
    reason : String

record OpportunityWindow : Set where
  constructor opportunityWindow
  field
    optionLabel openingTime closingTime : String
    expiredWithoutSelection : Bool
    rejectedAfterWeighing : Bool
    windowReceipt : String

record ProcessBearingBranch : Set where
  constructor processBearingBranch
  field
    branchId : String
    branchKind : BranchKind
    propositionNode : Response.PropositionNode
    outcomeStatus : OutcomeStatus
    branchStatus : BranchStatus
    processState : SearchState
    reusableSearchCapital : Nat
    sunkWork : Nat
    liveness : List LivenessWitness
    opportunities : List OpportunityWindow
    externalDependencies : List String
    servicingCost : Nat
    attractorAlignment : AttractorAlignment
    branchPhase : Nat
    provenance : List String

open ProcessBearingBranch public

record PairwiseBranchInterference : Set where
  constructor pairwiseBranchInterference
  field
    left right : ProcessBearingBranch
    phaseRelation : PhaseRelation
    interferenceKind : InterferenceKind
    sharedResources : List String
    incompatibleRequirements : List String
    interferenceReceipt : String

record BranchFamily : Set where
  constructor branchFamily
  field
    coarseGoal : String
    fineBranches : List ProcessBearingBranch
    pairwiseRelations : List PairwiseBranchInterference
    availableCapacity : Nat
    totalServicingDemand : Nat
    desiredAttractor : String
    familyReceipt : String

record BranchSelectionCriterion : Set where
  field
    respectsCapacity : Bool
    improvesAttractorReachability : Bool
    preservesUsefulOptionality : Bool
    valuesInformationGain : Bool
    penalisesDestructiveInterference : Bool
    distinguishesActivityFromProgress : Bool

canonicalBranchSelectionCriterion : BranchSelectionCriterion
canonicalBranchSelectionCriterion = record
  { respectsCapacity = true
  ; improvesAttractorReachability = true
  ; preservesUsefulOptionality = true
  ; valuesInformationGain = true
  ; penalisesDestructiveInterference = true
  ; distinguishesActivityFromProgress = true
  }

------------------------------------------------------------------------
-- PNF memory: retain branch status and provenance rather than quotienting all
-- unrealised outcomes into one terminal zero.
------------------------------------------------------------------------

record BranchMemory : Set where
  constructor branchMemory
  field
    rememberedBranch : ProcessBearingBranch
    statusHistory : List BranchStatus
    retainedAlternatives : List String
    unresolvedResidual : PNF.ComparisonResult
    pathProvenanceRetained : Bool
    capacityAtRelevantTime : Core.CapacityState
    memoryReceipt : String

record TraumaDeformation : Set where
  constructor traumaDeformation
  field
    triggeringPattern : String
    previouslyLostBranches : List String
    futureBranchHoardingRisk : Bool
    prematurePruningRisk : Bool
    threatMonitoringCost : Nat
    reconstructionCost : Nat
    contextSensitiveTransport : Bool
    deformationReceipt : String

record ProcessTransfer : Set where
  constructor processTransfer
  field
    branch : ProcessBearingBranch
    priorRepresentative successor : Core.Participant
    stateTransferred : Bool
    authorityTransferred : Bool
    recipientAccepted : Bool
    deadlinesPreserved : Bool
    liveApplicationsPreserved : Bool
    transferReceipt : String

------------------------------------------------------------------------
-- Typed hyperfabric: participants are vertices; process branches are edges.
------------------------------------------------------------------------

participantStalk : Core.Participant → Set
participantStalk participant = Core.CapacityState

branchStalk : ProcessBearingBranch → Set
branchStalk branch = BranchMemory

data IncidentTo : Core.Participant → ProcessBearingBranch → Set where
  servicesBranch :
    (participant : Core.Participant) →
    (branch : ProcessBearingBranch) →
    IncidentTo participant branch

restrictParticipantToBranch :
  ∀ {participant branch} →
  IncidentTo participant branch →
  participantStalk participant →
  branchStalk branch
restrictParticipantToBranch {participant} {branch} membership capacity =
  branchMemory
    branch
    (branchStatus branch ∷ [])
    []
    PNF.residuallyDifferent
    true
    capacity
    "participant capacity restricted to process-bearing branch"

branchProvenance : ProcessBearingBranch → List String
branchProvenance = provenance

branchSalience : ProcessBearingBranch → Nat
branchSalience branch = servicingCost branch

canonicalRelationalProcessHyperfabric :
  Hyperfabric.TypedHyperfabric Core.Participant ProcessBearingBranch
canonicalRelationalProcessHyperfabric = record
  { vertexStalk = participantStalk
  ; edgeStalk = branchStalk
  ; incidence = IncidentTo
  ; restrict = restrictParticipantToBranch
  ; edgeProvenance = branchProvenance
  ; edgeSalience = branchSalience
  ; fabricLabel = "relational process-bearing decision hyperfabric"
  }

record ProcessMemoryAuthorityBoundary : Set where
  field
    noOutcomeMeansNoProcess : Bool
    namedOptionMeansFeasibleOption : Bool
    expiredMeansRejected : Bool
    revocationErasesProcessState : Bool
    moreBranchesAlwaysImproveOutcome : Bool
    highActivityProvesAttractorProgress : Bool
    traumaDeformationIsDiagnosis : Bool
    boundaryNote : String

canonicalProcessMemoryAuthorityBoundary : ProcessMemoryAuthorityBoundary
canonicalProcessMemoryAuthorityBoundary = record
  { noOutcomeMeansNoProcess = false
  ; namedOptionMeansFeasibleOption = false
  ; expiredMeansRejected = false
  ; revocationErasesProcessState = false
  ; moreBranchesAlwaysImproveOutcome = false
  ; highActivityProvesAttractorProgress = false
  ; traumaDeformationIsDiagnosis = false
  ; boundaryNote =
      "Branches may be stateful, costly, perishable and partly exogenous before an outcome exists. PNF memory retains path, liveness layer, capacity and provenance without turning the model into a clinical diagnosis."
  }
