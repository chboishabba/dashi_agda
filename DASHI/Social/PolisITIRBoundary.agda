module DASHI.Social.PolisITIRBoundary where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- Pol.is / ITIR formal boundary.
--
-- Pol.is is treated as an external deliberation sidecar.  Its analytic
-- input is only the participant × statement opinion matrix.  Statement
-- text may be carried for display and later ITIR curation, but it is not
-- an input to the clustering/consensus operator formalised here.
--
-- ITIR supplies ontology-grounded seed frames and receives empirical
-- deliberation observations.  Those observations remain candidates:
-- they carry no truth, legal, theorem, or promotion authority by
-- themselves.

------------------------------------------------------------------------
-- Finite helpers.

listCount : ∀ {A : Set} → List A → Nat
listCount [] = zero
listCount (_ ∷ xs) = suc (listCount xs)

------------------------------------------------------------------------
-- Opinion-matrix vocabulary.

data Vote : Set where
  agree : Vote
  disagree : Vote
  pass : Vote

record OpinionCell : Set where
  constructor opinionCell
  field
    participantId : String
    statementId : String
    vote : Vote
open OpinionCell public

OpinionMatrix : Set
OpinionMatrix = List OpinionCell

record StatementText : Set where
  constructor statementText
  field
    textStatementId : String
    textBody : String
open StatementText public

StatementCorpus : Set
StatementCorpus = List StatementText

------------------------------------------------------------------------
-- Pol.is analytics are matrix-only.

record PolisAnalysis : Set where
  constructor polisAnalysis
  field
    analysisLabel : String
    participantClusterPayload : String
    statementStatisticsPayload : String
    bridgeStatementPayload : String
open PolisAnalysis public

PolisEngine : Set
PolisEngine = OpinionMatrix → PolisAnalysis

runPolis : PolisEngine → OpinionMatrix → PolisAnalysis
runPolis engine matrix = engine matrix

-- The statement corpus is deliberately absent from the engine type.
-- Therefore replacing, translating, or omitting display text cannot alter
-- a result for a fixed engine and fixed matrix.

textIndependent :
  (engine : PolisEngine) →
  (matrix : OpinionMatrix) →
  (left right : StatementCorpus) →
  runPolis engine matrix ≡ runPolis engine matrix
textIndependent engine matrix left right = refl

languageAgnosticAtMatrixBoundary :
  (engine : PolisEngine) →
  (matrix : OpinionMatrix) →
  (english māori arabic : StatementCorpus) →
  runPolis engine matrix ≡ runPolis engine matrix
languageAgnosticAtMatrixBoundary engine matrix english māori arabic = refl

------------------------------------------------------------------------
-- ITIR ontology frames and Pol.is seed statements.

data ITIRFrameKind : Set where
  protectedInterestFrame : ITIRFrameKind
  wrongTypeFrame : ITIRFrameKind
  valueFrame : ITIRFrameKind
  remedyFrame : ITIRFrameKind
  claimFrame : ITIRFrameKind

record ITIRFrame : Set where
  constructor itirFrame
  field
    frameId : String
    frameKind : ITIRFrameKind
    frameLabel : String
    provenanceAnchor : String
open ITIRFrame public

record PolisSeedStatement : Set where
  constructor polisSeedStatement
  field
    seedStatementId : String
    seedFrameId : String
    seedText : String
    atomic : Bool
    humanReviewRequired : Bool
open PolisSeedStatement public

SeedGenerator : Set
SeedGenerator = ITIRFrame → PolisSeedStatement

------------------------------------------------------------------------
-- Imported observations and candidate-only mappings.

data PolisObservationKind : Set where
  clusterObservation : PolisObservationKind
  consensusObservation : PolisObservationKind
  bridgeObservation : PolisObservationKind
  polarisationObservation : PolisObservationKind
  statementStatisticsObservation : PolisObservationKind

record PolisObservation : Set where
  constructor polisObservation
  field
    conversationId : String
    observationKind : PolisObservationKind
    observationPayload : String
    exportReceipt : String
open PolisObservation public

record OntologyMappingCandidate : Set where
  constructor ontologyMappingCandidate
  field
    mappedStatementId : String
    mappedFrameId : String
    mappingBasis : String
    confidenceLabel : String
    candidateOnly : Bool
    promoted : Bool
    carriesTruthAuthority : Bool
    carriesLegalAuthority : Bool
    carriesTheoremAuthority : Bool
open OntologyMappingCandidate public

mkMappingCandidate :
  String → String → String → String → OntologyMappingCandidate
mkMappingCandidate statement frame basis confidence =
  ontologyMappingCandidate
    statement
    frame
    basis
    confidence
    true
    false
    false
    false
    false

record MappingCandidateReceipt
  (candidate : OntologyMappingCandidate) : Set where
  constructor mappingCandidateReceipt
  field
    candidateOnlyIsTrue : candidateOnly candidate ≡ true
    promotedIsFalse : promoted candidate ≡ false
    noTruthAuthority : carriesTruthAuthority candidate ≡ false
    noLegalAuthority : carriesLegalAuthority candidate ≡ false
    noTheoremAuthority : carriesTheoremAuthority candidate ≡ false
open MappingCandidateReceipt public

canonicalMappingCandidateReceipt :
  (statement frame basis confidence : String) →
  MappingCandidateReceipt (mkMappingCandidate statement frame basis confidence)
canonicalMappingCandidateReceipt statement frame basis confidence =
  mappingCandidateReceipt refl refl refl refl refl

------------------------------------------------------------------------
-- Governance boundary: empirical support is evidence, not truth.

data PromotionDecision : Set where
  abstain : PromotionDecision
  reject : PromotionDecision
  promoteWithReceipt : PromotionDecision

record ITIRGovernanceGate : Set where
  constructor itirGovernanceGate
  field
    governanceLabel : String
    requiresSourceProvenance : Bool
    requiresHumanReview : Bool
    preservesAbstention : Bool
    decision : PromotionDecision
open ITIRGovernanceGate public

canonicalGovernanceGate : PromotionDecision → ITIRGovernanceGate
canonicalGovernanceGate selectedDecision =
  itirGovernanceGate
    "ITIR governance gate"
    true
    true
    true
    selectedDecision

------------------------------------------------------------------------
-- O / R / C / S / L / P / G / F placement.

record PolisITIRORCSLPGF : Set where
  constructor polisITIRORCSLPGF
  field
    O-organisations : String
    R-request : String
    C-capability : String
    S-state : String
    L-lattice : String
    P-proposal : String
    G-governance : String
    F-gap : String
open PolisITIRORCSLPGF public

canonicalPolisITIRModel : PolisITIRORCSLPGF
canonicalPolisITIRModel =
  polisITIRORCSLPGF
    "ITIR authors, participants, facilitators, and Pol.is sidecar"
    "test ontology-grounded statements through public deliberation"
    "seed export, opinion-matrix analysis, result import, curated mapping"
    "frames, statements, votes, clusters, bridge statistics, receipts"
    "raw export < imported observation < curated candidate < governed promotion"
    "candidate support overlays for interests, wrongs, values, remedies, claims"
    "ITIR provenance and human-review promotion gate"
    "unmapped statements, ambiguous mappings, missing receipts, or unreviewed promotion"

------------------------------------------------------------------------
-- Explicit reuse / non-reimplementation contract.

record ReuseContract : Set where
  constructor reuseContract
  field
    reusePolisCollection : Bool
    reusePolisOpinionMatrix : Bool
    reusePolisClustering : Bool
    reusePolisBridgeStatistics : Bool
    doNotUseNLPInsidePolisAnalysis : Bool
    doNotRebuildVotingUI : Bool
    doNotPromoteImportedClustersDirectly : Bool
open ReuseContract public

canonicalReuseContract : ReuseContract
canonicalReuseContract =
  reuseContract true true true true true true true

------------------------------------------------------------------------
-- Key deliverables captured as a bounded implementation surface.

data Deliverable : Set where
  sidecarArchitectureDecision : Deliverable
  ontologySeedExportSchema : Deliverable
  polisConversationAdapter : Deliverable
  polisExportImportSchema : Deliverable
  opinionMatrixReceipt : Deliverable
  statementOntologyMappingCandidates : Deliverable
  humanCurationGate : Deliverable
  consensusOverlayProjection : Deliverable
  provenanceAndAsAtReceipt : Deliverable
  noNLPRegressionTest : Deliverable

keyDeliverables : List Deliverable
keyDeliverables =
  sidecarArchitectureDecision
  ∷ ontologySeedExportSchema
  ∷ polisConversationAdapter
  ∷ polisExportImportSchema
  ∷ opinionMatrixReceipt
  ∷ statementOntologyMappingCandidates
  ∷ humanCurationGate
  ∷ consensusOverlayProjection
  ∷ provenanceAndAsAtReceipt
  ∷ noNLPRegressionTest
  ∷ []

keyDeliverableCount : Nat
keyDeliverableCount = listCount keyDeliverables

------------------------------------------------------------------------
-- End-to-end boundary packet.

record PolisITIRRoundTrip : Set where
  constructor polisITIRRoundTrip
  field
    sourceFrame : ITIRFrame
    exportedSeed : PolisSeedStatement
    importedObservation : PolisObservation
    mappingCandidate : OntologyMappingCandidate
    governanceGate : ITIRGovernanceGate
    reuseContractReceipt : ReuseContract
open PolisITIRRoundTrip public

roundTripCandidateNotPromoted :
  (frame : ITIRFrame) →
  (seed : PolisSeedStatement) →
  (observation : PolisObservation) →
  (statement frameId basis confidence : String) →
  promoted
    (mappingCandidate
      (polisITIRRoundTrip
        frame
        seed
        observation
        (mkMappingCandidate statement frameId basis confidence)
        (canonicalGovernanceGate abstain)
        canonicalReuseContract))
  ≡ false
roundTripCandidateNotPromoted frame seed observation statement frameId basis confidence = refl
