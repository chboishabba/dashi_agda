module DASHI.Interop.PolisITIRDeliberationBoundary where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- Pol.is <-> ITIR deliberation sidecar boundary.
--
-- Pol.is owns statement voting, participant x statement matrices, clustering,
-- and bridge/consensus statistics without semantic NLP.  ITIR/SensiBlaw may
-- seed human-readable statements from ontology nodes and may map imported
-- statement results back to ontology nodes after deliberation.  Imported
-- support is empirical/advisory and never normative or legal authority.

data PolisVote : Set where
  agreeVote : PolisVote
  disagreeVote : PolisVote
  passVote : PolisVote

data StatementOrigin : Set where
  itirSeededStatement : StatementOrigin
  participantAuthoredStatement : StatementOrigin

data ITIROntologyTargetKind : Set where
  valueFrameTarget : ITIROntologyTargetKind
  protectedInterestTarget : ITIROntologyTargetKind
  wrongTypeTarget : ITIROntologyTargetKind
  remedyTarget : ITIROntologyTargetKind
  claimTarget : ITIROntologyTargetKind
  communityConceptTarget : ITIROntologyTargetKind

record PolisStatement : Set where
  constructor polisStatement
  field
    statementId : String
    conversationId : String
    statementText : String
    origin : StatementOrigin

record PolisVoteRow : Set where
  constructor polisVoteRow
  field
    participantId : String
    votedStatementId : String
    vote : PolisVote

record PolisClusterRow : Set where
  constructor polisClusterRow
  field
    clusterId : String
    clusterLabel : String
    participantCount : Nat

record PolisStatementStatistic : Set where
  constructor polisStatementStatistic
  field
    statisticStatementId : String
    agreeCount : Nat
    disagreeCount : Nat
    passCount : Nat
    bridgeScorePermille : Nat
    consensusScorePermille : Nat

record PolisStatementMapping : Set where
  constructor polisStatementMapping
  field
    mappedStatementId : String
    targetKind : ITIROntologyTargetKind
    targetInternalId : Nat
    mappingSource : String
    mappingConfidencePermille : Nat
    humanConfirmed : Bool

record PolisConversationImport : Set where
  constructor polisConversationImport
  field
    importedConversationId : String
    statements : List PolisStatement
    votes : List PolisVoteRow
    clusters : List PolisClusterRow
    statistics : List PolisStatementStatistic
    ontologyMappings : List PolisStatementMapping

record PolisAuthorityBits : Set where
  field
    ownsVotingInterface : Bool
    ownsVotingInterfaceIsTrue : ownsVotingInterface ≡ true
    ownsVoteMatrix : Bool
    ownsVoteMatrixIsTrue : ownsVoteMatrix ≡ true
    ownsSocialClustering : Bool
    ownsSocialClusteringIsTrue : ownsSocialClustering ≡ true
    ownsBridgeStatistics : Bool
    ownsBridgeStatisticsIsTrue : ownsBridgeStatistics ≡ true
    usesSemanticNLPForConsensus : Bool
    usesSemanticNLPForConsensusIsFalse : usesSemanticNLPForConsensus ≡ false
    ownsLegalOntology : Bool
    ownsLegalOntologyIsFalse : ownsLegalOntology ≡ false
    ownsNormativeAuthority : Bool
    ownsNormativeAuthorityIsFalse : ownsNormativeAuthority ≡ false

record ITIRDeliberationAuthorityBits : Set where
  field
    maySeedStatementsFromOntology : Bool
    maySeedStatementsFromOntologyIsTrue : maySeedStatementsFromOntology ≡ true
    mapsResultsAfterImport : Bool
    mapsResultsAfterImportIsTrue : mapsResultsAfterImport ≡ true
    participantStatementsRequireCuration : Bool
    participantStatementsRequireCurationIsTrue :
      participantStatementsRequireCuration ≡ true
    communitySupportIsEmpirical : Bool
    communitySupportIsEmpiricalIsTrue : communitySupportIsEmpirical ≡ true
    communitySupportIsNormativeTruth : Bool
    communitySupportIsNormativeTruthIsFalse :
      communitySupportIsNormativeTruth ≡ false
    communitySupportIsLegalAuthority : Bool
    communitySupportIsLegalAuthorityIsFalse :
      communitySupportIsLegalAuthority ≡ false
    reimplementsPolisConsensusEngine : Bool
    reimplementsPolisConsensusEngineIsFalse :
      reimplementsPolisConsensusEngine ≡ false

open PolisAuthorityBits public
open ITIRDeliberationAuthorityBits public

canonicalPolisAuthorityBits : PolisAuthorityBits
canonicalPolisAuthorityBits =
  record
    { ownsVotingInterface = true
    ; ownsVotingInterfaceIsTrue = refl
    ; ownsVoteMatrix = true
    ; ownsVoteMatrixIsTrue = refl
    ; ownsSocialClustering = true
    ; ownsSocialClusteringIsTrue = refl
    ; ownsBridgeStatistics = true
    ; ownsBridgeStatisticsIsTrue = refl
    ; usesSemanticNLPForConsensus = false
    ; usesSemanticNLPForConsensusIsFalse = refl
    ; ownsLegalOntology = false
    ; ownsLegalOntologyIsFalse = refl
    ; ownsNormativeAuthority = false
    ; ownsNormativeAuthorityIsFalse = refl
    }

canonicalITIRDeliberationAuthorityBits : ITIRDeliberationAuthorityBits
canonicalITIRDeliberationAuthorityBits =
  record
    { maySeedStatementsFromOntology = true
    ; maySeedStatementsFromOntologyIsTrue = refl
    ; mapsResultsAfterImport = true
    ; mapsResultsAfterImportIsTrue = refl
    ; participantStatementsRequireCuration = true
    ; participantStatementsRequireCurationIsTrue = refl
    ; communitySupportIsEmpirical = true
    ; communitySupportIsEmpiricalIsTrue = refl
    ; communitySupportIsNormativeTruth = false
    ; communitySupportIsNormativeTruthIsFalse = refl
    ; communitySupportIsLegalAuthority = false
    ; communitySupportIsLegalAuthorityIsFalse = refl
    ; reimplementsPolisConsensusEngine = false
    ; reimplementsPolisConsensusEngineIsFalse = refl
    }

record PolisITIRDeliberationBoundary : Set where
  field
    sampleImport : PolisConversationImport
    polisAuthority : PolisAuthorityBits
    itirAuthority : ITIRDeliberationAuthorityBits
    voteMatrixPrecedesSemanticMapping : Bool
    voteMatrixPrecedesSemanticMappingIsTrue :
      voteMatrixPrecedesSemanticMapping ≡ true
    seededStatementsRetainOriginIds : Bool
    seededStatementsRetainOriginIdsIsTrue :
      seededStatementsRetainOriginIds ≡ true
    notes : List String

open PolisITIRDeliberationBoundary public

canonicalPolisITIRDeliberationBoundary : PolisITIRDeliberationBoundary
canonicalPolisITIRDeliberationBoundary =
  record
    { sampleImport =
        polisConversationImport
          "conversation-0"
          []
          []
          []
          []
          []
    ; polisAuthority = canonicalPolisAuthorityBits
    ; itirAuthority = canonicalITIRDeliberationAuthorityBits
    ; voteMatrixPrecedesSemanticMapping = true
    ; voteMatrixPrecedesSemanticMappingIsTrue = refl
    ; seededStatementsRetainOriginIds = true
    ; seededStatementsRetainOriginIdsIsTrue = refl
    ; notes =
        "Pol.is remains the deliberation sidecar: statement atoms, votes, clusters, and bridge statistics."
      ∷ "Consensus clustering is social-matrix analysis rather than semantic NLP."
      ∷ "ITIR maps imported results to ValueFrames, ProtectedInterests, WrongTypes, Remedies, Claims, or curated community concepts only after import."
      ∷ "Community support may calibrate priorities but cannot establish legal, moral, or factual truth."
      ∷ []
    }
