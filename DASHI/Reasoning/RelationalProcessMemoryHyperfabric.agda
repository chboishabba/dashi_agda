module DASHI.Reasoning.RelationalProcessMemoryHyperfabric where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)
open import Data.Integer using (ℤ) renaming (_+_ to _+ℤ_)
open import Data.List.Base using (map)

import DASHI.Cognition.PNF.EventAlgebra as PNF
import DASHI.Physics.ShiftDiscreteWaveStep as Wave
import DASHI.Physics.ShiftPhaseTableInterference as Phase
import DASHI.Reasoning.TypedHyperfabricCore as Hyperfabric
import DASHI.Reasoning.RelationalStateCore as Core
import DASHI.Reasoning.ConditionalResponseTree as Response
import DASHI.Reasoning.AttractorAlignedBranchSelection as Selection
import DASHI.Reasoning.RelationalBranchInterference as Interference

------------------------------------------------------------------------
-- Typed list membership used for actual hyperfabric incidence.
------------------------------------------------------------------------

data _∈_ {A : Set} (x : A) : List A → Set where
  here : ∀ {xs} → x ∈ (x ∷ xs)
  there : ∀ {y xs} → x ∈ xs → x ∈ (y ∷ xs)

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
    assignedParticipants : List Core.Participant
    servicingCost : Nat
    attractorAlignment : AttractorAlignment
    branchPhase : Nat
    branchWaveAmplitude : Nat
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

------------------------------------------------------------------------
-- Exact qualitative -> quantitative branch derivation.
------------------------------------------------------------------------

phaseFromNat : Nat → Phase.Phase4
phaseFromNat zero = Phase.φ0
phaseFromNat (suc zero) = Phase.φ1
phaseFromNat (suc (suc zero)) = Phase.φ2
phaseFromNat (suc (suc (suc zero))) = Phase.φ3
phaseFromNat (suc (suc (suc (suc n)))) = phaseFromNat n

qualitativeBranchWave : ProcessBearingBranch → Interference.BranchWave
qualitativeBranchWave branch =
  Wave.waveOfData
    (branchWaveAmplitude branch)
    (phaseFromNat (branchPhase branch))

record MetricDerivation
    (source : ProcessBearingBranch)
    (metric : Selection.BranchMetric) : Set where
  constructor metricDerivation
  field
    branchIdentityPreserved :
      Selection.branchLabel metric ≡ branchId source
    servicingCostPreserved :
      Selection.servicingCost metric ≡ servicingCost source
    additionalMetricFieldsAreExplicitRefinements : String

open MetricDerivation public

record QuantitativeBranchRefinement : Set where
  constructor quantitativeBranchRefinement
  field
    qualitativeBranch : ProcessBearingBranch
    selectionMetric : Selection.BranchMetric
    branchWave : Interference.BranchWave
    metricDerivationWitness :
      MetricDerivation qualitativeBranch selectionMetric
    branchWaveDerivation :
      branchWave ≡ qualitativeBranchWave qualitativeBranch
    metricIsCandidateOnly : Bool
    phaseIsCompatibilityAnalogyOnly : Bool
    refinementReceipt : String

open QuantitativeBranchRefinement public

------------------------------------------------------------------------
-- Synchronized family refinement.
--
-- One refinement list is authoritative.  Three equality witnesses prove that
-- the qualitative family, portfolio metrics, and wave list are exactly its
-- projections.  Foreign metrics/waves and missing/duplicated coverage are not
-- representable by a QuantitativeFamilyRefinement.
------------------------------------------------------------------------

record QuantitativeFamilyRefinement : Set where
  constructor quantitativeFamilyRefinement
  field
    qualitativeFamily : BranchFamily
    selectionPortfolio : Selection.BranchPortfolio
    branchRefinements : List QuantitativeBranchRefinement
    branchWaves : List Interference.BranchWave
    waveBackedInteractions : List Interference.WaveBackedInteraction
    qualitativeCoverage :
      fineBranches qualitativeFamily
      ≡ map qualitativeBranch branchRefinements
    metricCoverage :
      Selection.branches selectionPortfolio
      ≡ map selectionMetric branchRefinements
    waveCoverage :
      branchWaves ≡ map branchWave branchRefinements
    exactNSlitReceipt :
      Interference.coherentIntensity branchWaves
      ≡
      Interference.diagonalIntensity branchWaves
      +ℤ Interference.allPairwiseInterference branchWaves
    portfolioAndWaveWeightsEmpiricallyCalibrated : Bool
    familyRefinementReceipt : String

record BranchSelectionCriterion : Set where
  field
    respectsCapacity : Bool
    improvesAttractorReachability : Bool
    preservesUsefulOptionality : Bool
    valuesInformationGain : Bool
    penalisesDestructiveInterference : Bool
    distinguishesActivityFromProgress : Bool
    quotientsNominalOptionsByReachableBasin : Bool
    checksLocalUtilityAgainstGlobalDrift : Bool
    requiresSynchronizedQualitativeMetricWaveCoverage : Bool

canonicalBranchSelectionCriterion : BranchSelectionCriterion
canonicalBranchSelectionCriterion = record
  { respectsCapacity = true
  ; improvesAttractorReachability = true
  ; preservesUsefulOptionality = true
  ; valuesInformationGain = true
  ; penalisesDestructiveInterference = true
  ; distinguishesActivityFromProgress = true
  ; quotientsNominalOptionsByReachableBasin = true
  ; checksLocalUtilityAgainstGlobalDrift = true
  ; requiresSynchronizedQualitativeMetricWaveCoverage = true
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
    ∀ {participant branch} →
    participant ∈ assignedParticipants branch →
    IncidentTo participant branch

restrictParticipantToBranch :
  ∀ {participant branch} →
  IncidentTo participant branch →
  participantStalk participant →
  branchStalk branch
restrictParticipantToBranch {branch = branch} membership capacity =
  branchMemory
    branch
    (branchStatus branch ∷ [])
    []
    PNF.residuallyDifferent
    true
    capacity
    "assigned participant capacity restricted to process-bearing branch"

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
    qualitativeAlignmentIsFinalMathematics : Bool
    literalQuantumDecisionDynamicsClaimed : Bool
    quantitativePromotionRequiresReceipt : Bool
    quantitativeFamilyAllowsForeignMetricsOrWaves : Bool
    arbitraryParticipantIncidentToEveryBranch : Bool
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
  ; qualitativeAlignmentIsFinalMathematics = false
  ; literalQuantumDecisionDynamicsClaimed = false
  ; quantitativePromotionRequiresReceipt = true
  ; quantitativeFamilyAllowsForeignMetricsOrWaves = false
  ; arbitraryParticipantIncidentToEveryBranch = false
  ; traumaDeformationIsDiagnosis = false
  ; boundaryNote =
      "Branches may be stateful, costly, perishable and partly exogenous before an outcome exists. Exact selection and n-slit layers require synchronized qualitative/metric/wave refinements, and hyperfabric incidence requires typed participant assignment. PNF memory retains path, liveness, capacity and provenance without becoming a clinical or quantum diagnosis."
  }
