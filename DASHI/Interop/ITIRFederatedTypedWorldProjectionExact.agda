module DASHI.Interop.ITIRFederatedTypedWorldProjectionExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Interop.DistributedEpistemicPlaneSeparationExact as Fabric
import DASHI.Interop.DistributedEvidenceHistoryProjectionExact as EvidenceHistory
import DASHI.Interop.DistributedProofProducerABIExact as ProofABI
import DASHI.Applications.CounterUASWorldMonitorEvidenceHealthBridgeExact as WorldMonitor
import DASHI.Social.StreamsEngineBoundary as Streams

------------------------------------------------------------------------
-- ITIR FEDERATED TYPED WORLD + SOURCE-ADDRESSABLE PROJECTION
--
-- This owner composes already-existing DASHI/ITIR boundaries. It does not
-- introduce another evidence ontology or transfer authority between systems.
--
-- Intended suite roles:
--   * semantic/formal world: epistemic construction and typed interpretation;
--   * StatiBaker: temporal observer state / replay memory;
--   * Casey: candidate/workspace/collapse/build authority;
--   * SensibLaw/SLR: semantic/legal review, admission and legal projection;
--   * itir-ribbon: projection-only UI;
--   * dashi_agda: exploratory/golden reference;
--   * dashi_lean4: progressively consolidated formal/reference + executable
--     checker/prover/worker implementation.
------------------------------------------------------------------------

data StateAuthority : Set where
  semanticWorldAuthority : StateAuthority
  temporalObserverAuthority : StateAuthority
  possibilityWorkspaceAuthority : StateAuthority
  legalAdmissionAuthority : StateAuthority
  projectionOnlyAuthority : StateAuthority
  formalWorkerAuthority : StateAuthority

data WorldObjectRole : Set where
  observationRole : WorldObjectRole
  occurrenceRole : WorldObjectRole
  assertionReportRole : WorldObjectRole
  entityHypothesisRole : WorldObjectRole
  clusterRole : WorldObjectRole
  forecastRole : WorldObjectRole
  alertRole : WorldObjectRole
  rollingBaselineStateRole : WorldObjectRole
  candidateAlternativeRole : WorldObjectRole
  derivedPatternRole : WorldObjectRole
  formalResultRole : WorldObjectRole
  reviewAdmissionRole : WorldObjectRole
  residualGapRole : WorldObjectRole

data ProjectionKind : Set where
  explainProjection : ProjectionKind
  whyProjection : ProjectionKind
  sourceProjection : ProjectionKind
  contextProjection : ProjectionKind
  graphProjection : ProjectionKind
  timelineProjection : ProjectionKind
  ribbonSankeyProjection : ProjectionKind
  proofTreeProjection : ProjectionKind
  citationProjection : ProjectionKind

data TypedRefinementKind : Set where
  studyDesignRefinement : TypedRefinementKind
  healthSensorRefinement : TypedRefinementKind
  financeFlowRefinement : TypedRefinementKind
  wikidataStatementRefinement : TypedRefinementKind
  legalAuthorityRefinement : TypedRefinementKind
  testimonialRefinement : TypedRefinementKind
  formalProofRefinement : TypedRefinementKind
  namedRefinement : String → TypedRefinementKind

record SourceAddressableSemanticNode : Set where
  constructor sourceAddressableSemanticNode
  field
    semanticIdentity : String
    sourceIdentity : String
    sourceRevision : String
    sourceAnchors : List Streams.SourceAnchor
    producerReceiptRef : String
    reviewReceiptRef : String
    dependencySummary : String
    residualSummary : String
    exactSourceRetained : Bool
    exactSourceRetainedIsTrue : exactSourceRetained ≡ true
    projectionChangesIdentity : Bool
    projectionChangesIdentityIsFalse : projectionChangesIdentity ≡ false
    nodeCreatesClaimTruth : Bool
    nodeCreatesClaimTruthIsFalse : nodeCreatesClaimTruth ≡ false

open SourceAddressableSemanticNode public

record TypedRefinement : Set where
  constructor typedRefinement
  field
    refinedNode : SourceAddressableSemanticNode
    refinementKind : TypedRefinementKind
    refinementPayloadRef : String
    refinementCreatesCanonicalEvidenceUniverse : Bool
    refinementCreatesCanonicalEvidenceUniverseIsFalse :
      refinementCreatesCanonicalEvidenceUniverse ≡ false
    refinementCreatesConsumerConclusion : Bool
    refinementCreatesConsumerConclusionIsFalse :
      refinementCreatesConsumerConclusion ≡ false

open TypedRefinement public

record SemanticProjection : Set where
  constructor semanticProjection
  field
    projectedNode : SourceAddressableSemanticNode
    projectionKind : ProjectionKind
    renderedSurfaceRef : String
    projectionOwnsCanonicalTruth : Bool
    projectionOwnsCanonicalTruthIsFalse :
      projectionOwnsCanonicalTruth ≡ false

open SemanticProjection public

record SuiteRoleMap : Set where
  constructor suiteRoleMap
  field
    sensibLawRole : String
    statiBakerRole : String
    caseyRole : String
    worldMonitorRole : String
    ribbonRole : String
    agdaRole : String
    leanRole : String

open SuiteRoleMap public

canonicalSuiteRoleMap : SuiteRoleMap
canonicalSuiteRoleMap =
  suiteRoleMap
    "SensibLaw/SLR: review/admission, semantic construction and legal consumer projection"
    "StatiBaker: temporal observer state, continuity, receipts and deterministic replay"
    "casey-git-clone: candidate/workspace/selection/collapse/build authority"
    "WorldMonitor-style world surface: evidence health, gaps, baselines and external observation state"
    "itir-ribbon/Streamline: projection-only timeline/ribbon/Sankey views"
    "dashi_agda: exploratory/golden formal/reference corpus"
    "dashi_lean4: consolidation target for formal/reference models plus executable checker/prover/worker programs"

------------------------------------------------------------------------
-- Existing owner reuse.
------------------------------------------------------------------------

worldMonitorEvidenceHealthReceipt : WorldMonitor.EvidenceHealthReceipt
worldMonitorEvidenceHealthReceipt =
  WorldMonitor.canonicalHealthyEvidenceReceipt

distributedEvidenceHistoryReceipt : EvidenceHistory.AuditableDerivedViewReceipt
distributedEvidenceHistoryReceipt =
  EvidenceHistory.exampleAuditableDerivedView

leanWorkerABI : ProofABI.ProofProducerABI
leanWorkerABI = ProofABI.leanWikiProverABI

distributedPlanePath : List Fabric.EpistemicPlane
distributedPlanePath = Fabric.canonicalPlanePath

------------------------------------------------------------------------
-- Projection preserves one semantic identity across reading surfaces.
------------------------------------------------------------------------

sameSemanticTarget :
  SourceAddressableSemanticNode →
  ProjectionKind →
  SourceAddressableSemanticNode
sameSemanticTarget node projection = node

projectionIdentityPreserved :
  (node : SourceAddressableSemanticNode) →
  (projection : ProjectionKind) →
  semanticIdentity (sameSemanticTarget node projection) ≡ semanticIdentity node
projectionIdentityPreserved node projection = refl

------------------------------------------------------------------------
-- Cross-suite non-collapse laws.
------------------------------------------------------------------------

data ObservationCreatesOccurrence : Set where
data ReportCreatesOccurrence : Set where
data MissingObservationCreatesObservedAbsence : Set where
data StaleEvidenceCreatesFalsehood : Set where
data SignalAgreementCreatesIndependentGenealogy : Set where
data CrossStreamAlignmentCreatesCausation : Set where
data TemporalObserverReceiptCreatesSemanticAuthority : Set where
data CaseySelectionCreatesWorldTruth : Set where
data ProjectionCreatesCanonicalState : Set where
data FormalProofCreatesExternalWorldTruth : Set where
data FormalArtifactCreatesProof : Set where
data TypedRefinementCreatesNewCanonicalEvidenceUniverse : Set where
data FinancePatternCreatesLegalWrong : Set where
data SensorPatternCreatesClinicalDiagnosis : Set where
data WikidataClassCreatesLegalCategory : Set where
data SourcePresenceCreatesApplicability : Set where

observationIsNotOccurrence : ObservationCreatesOccurrence → ⊥
observationIsNotOccurrence ()

reportIsNotOccurrence : ReportCreatesOccurrence → ⊥
reportIsNotOccurrence ()

missingObservationIsNotObservedAbsence :
  MissingObservationCreatesObservedAbsence → ⊥
missingObservationIsNotObservedAbsence ()

staleEvidenceIsNotFalsehood : StaleEvidenceCreatesFalsehood → ⊥
staleEvidenceIsNotFalsehood ()

signalAgreementIsNotIndependentGenealogy :
  SignalAgreementCreatesIndependentGenealogy → ⊥
signalAgreementIsNotIndependentGenealogy ()

crossStreamAlignmentIsNotCausation :
  CrossStreamAlignmentCreatesCausation → ⊥
crossStreamAlignmentIsNotCausation ()

temporalObserverReceiptIsNotSemanticAuthority :
  TemporalObserverReceiptCreatesSemanticAuthority → ⊥
temporalObserverReceiptIsNotSemanticAuthority ()

caseySelectionIsNotWorldTruth : CaseySelectionCreatesWorldTruth → ⊥
caseySelectionIsNotWorldTruth ()

projectionIsNotCanonicalState : ProjectionCreatesCanonicalState → ⊥
projectionIsNotCanonicalState ()

formalProofIsNotExternalWorldTruth :
  FormalProofCreatesExternalWorldTruth → ⊥
formalProofIsNotExternalWorldTruth ()

formalArtifactIsNotProof : FormalArtifactCreatesProof → ⊥
formalArtifactIsNotProof ()

typedRefinementIsNotNewCanonicalEvidenceUniverse :
  TypedRefinementCreatesNewCanonicalEvidenceUniverse → ⊥
typedRefinementIsNotNewCanonicalEvidenceUniverse ()

financePatternIsNotLegalWrong : FinancePatternCreatesLegalWrong → ⊥
financePatternIsNotLegalWrong ()

sensorPatternIsNotClinicalDiagnosis :
  SensorPatternCreatesClinicalDiagnosis → ⊥
sensorPatternIsNotClinicalDiagnosis ()

wikidataClassIsNotLegalCategory : WikidataClassCreatesLegalCategory → ⊥
wikidataClassIsNotLegalCategory ()

sourcePresenceIsNotApplicability : SourcePresenceCreatesApplicability → ⊥
sourcePresenceIsNotApplicability ()

------------------------------------------------------------------------
-- Sprint-3 ownership consequence.
------------------------------------------------------------------------

data SLRLegalGate : Set where
  reviewedWorldToWrongTypeGate : SLRLegalGate
  sourceRealisedLegalEvaluatorGate : SLRLegalGate
  adaptiveAustralianCapstoneGate : SLRLegalGate

canonicalSLRSprint3Gates : List SLRLegalGate
canonicalSLRSprint3Gates =
  reviewedWorldToWrongTypeGate
  ∷ sourceRealisedLegalEvaluatorGate
  ∷ adaptiveAustralianCapstoneGate
  ∷ []

slrBuildsSecondGlobalWorldModel : Bool
slrBuildsSecondGlobalWorldModel = false

digitalESDDefinesCoreEvidenceOntology : Bool
digitalESDDefinesCoreEvidenceOntology = false

ribbonOwnsFinanceTruth : Bool
ribbonOwnsFinanceTruth = false

statiBakerOwnsSemanticWorldTruth : Bool
statiBakerOwnsSemanticWorldTruth = false
