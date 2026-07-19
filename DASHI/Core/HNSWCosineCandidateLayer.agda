module DASHI.Core.HNSWCosineCandidateLayer where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.String using (String)

import DASHI.Core.CandidateOnlyCore as Candidate

------------------------------------------------------------------------
-- HNSW cosine candidate layer.
--
-- This module places approximate nearest-neighbour search in the DASHI
-- pipeline as a lossy access layer only:
--
--   typed object -> embedding projection -> HNSW cosine retrieval
--                -> candidate neighbourhood -> structural recheck
--
-- A returned neighbour is not thereby equal, subsuming, contradictory,
-- admissible, supported, true, or promoted.  Those relations remain external
-- proof obligations discharged by typed DASHI / PNF / residual machinery.
------------------------------------------------------------------------

record CosineProjectionCore : Set₁ where
  constructor mkCosineProjectionCore
  field
    coreLabel : String
    coreOwner : String

    objectType : Set
    vectorType : Set
    scoreType : Set

    embed : objectType → vectorType
    cosine : vectorType → vectorType → scoreType

open CosineProjectionCore public

record HNSWParameters : Set where
  constructor mkHNSWParameters
  field
    maximumConnections : Nat
    constructionSearchWidth : Nat
    querySearchWidth : Nat
    requestedNeighbourCount : Nat

open HNSWParameters public

record HNSWQuery (core : CosineProjectionCore) : Set where
  constructor mkHNSWQuery
  field
    queryObject : objectType core
    queryVector : vectorType core
    queryVectorIsEmbedding : queryVector ≡ embed core queryObject
    queryParameters : HNSWParameters

open HNSWQuery public

record HNSWCandidate
    (core : CosineProjectionCore)
    (query : HNSWQuery core) : Set where
  constructor mkHNSWCandidate
  field
    candidateObject : objectType core
    candidateVector : vectorType core
    candidateVectorIsEmbedding :
      candidateVector ≡ embed core candidateObject

    candidateCosineScore : scoreType core
    candidateScoreIsProjectedCosine :
      candidateCosineScore ≡
      cosine core (queryVector query) candidateVector

    graphLayer : Nat
    discoveryRank : Nat

open HNSWCandidate public

record HNSWRetrievalReceipt
    (core : CosineProjectionCore)
    (query : HNSWQuery core) : Set where
  constructor mkHNSWRetrievalReceipt
  field
    retrievalLabel : String
    candidates : List (HNSWCandidate core query)

    approximateNearestNeighbourOnly : Bool
    approximateNearestNeighbourOnlyIsTrue :
      approximateNearestNeighbourOnly ≡ true

    exhaustiveNearestNeighbourProof : Bool
    exhaustiveNearestNeighbourProofIsFalse :
      exhaustiveNearestNeighbourProof ≡ false

open HNSWRetrievalReceipt public

------------------------------------------------------------------------
-- Authority boundary.

record HNSWCosineAuthorityBoundary : Set where
  constructor mkHNSWCosineAuthorityBoundary
  field
    candidateGenerationOnly : Bool
    candidateGenerationOnlyIsTrue : candidateGenerationOnly ≡ true

    grantsObjectEquality : Bool
    grantsObjectEqualityIsFalse : grantsObjectEquality ≡ false

    grantsSubsumption : Bool
    grantsSubsumptionIsFalse : grantsSubsumption ≡ false

    grantsContradiction : Bool
    grantsContradictionIsFalse : grantsContradiction ≡ false

    grantsAdmissibility : Bool
    grantsAdmissibilityIsFalse : grantsAdmissibility ≡ false

    grantsSupport : Bool
    grantsSupportIsFalse : grantsSupport ≡ false

    grantsTruth : Bool
    grantsTruthIsFalse : grantsTruth ≡ false

    grantsPromotion : Bool
    grantsPromotionIsFalse : grantsPromotion ≡ false

open HNSWCosineAuthorityBoundary public

canonicalHNSWCosineAuthorityBoundary : HNSWCosineAuthorityBoundary
canonicalHNSWCosineAuthorityBoundary =
  mkHNSWCosineAuthorityBoundary
    true refl
    false refl
    false refl
    false refl
    false refl
    false refl
    false refl
    false refl

------------------------------------------------------------------------
-- Typed structural recheck socket.
--
-- These relations are supplied by the downstream formal domain.  HNSW does
-- not define or decide them.  A candidate may only cross into a promoted lane
-- through a separate receipt containing the relevant proofs.

record StructuralRecheckFamily (core : CosineProjectionCore) : Set₁ where
  constructor mkStructuralRecheckFamily
  field
    roleCompatible : objectType core → objectType core → Set
    qualifierCompatible : objectType core → objectType core → Set
    provenanceAcceptable : objectType core → Set
    residualAcceptable : objectType core → objectType core → Set
    admissible : objectType core → objectType core → Set

open StructuralRecheckFamily public

record StructurallyRecheckedCandidate
    (core : CosineProjectionCore)
    (query : HNSWQuery core)
    (relations : StructuralRecheckFamily core)
    (candidate : HNSWCandidate core query) : Set where
  constructor mkStructurallyRecheckedCandidate
  field
    roleCompatibilityProof :
      roleCompatible relations
        (queryObject query)
        (candidateObject candidate)

    qualifierCompatibilityProof :
      qualifierCompatible relations
        (queryObject query)
        (candidateObject candidate)

    provenanceProof :
      provenanceAcceptable relations
        (candidateObject candidate)

    residualProof :
      residualAcceptable relations
        (queryObject query)
        (candidateObject candidate)

    admissibilityProof :
      admissible relations
        (queryObject query)
        (candidateObject candidate)

open StructurallyRecheckedCandidate public

record PromotionGate
    (core : CosineProjectionCore)
    (query : HNSWQuery core)
    (relations : StructuralRecheckFamily core)
    (candidate : HNSWCandidate core query) : Set where
  constructor mkPromotionGate
  field
    structuralReceipt :
      StructurallyRecheckedCandidate core query relations candidate

    independentlyPromoted : Bool
    independentlyPromotedIsTrue : independentlyPromoted ≡ true

open PromotionGate public

------------------------------------------------------------------------
-- Candidate-only integration.

hnswCosineCandidateRow : Candidate.CandidateOnlyRow
hnswCosineCandidateRow =
  Candidate.mkCandidateOnlyRow
    "HNSW cosine retrieval"
    "DASHI.Core.HNSWCosineCandidateLayer"
    "embedding projection / approximate graph neighbourhood"
    Candidate.rankingCandidateKind
    Candidate.rankingCandidateOnlyStatus
    "HNSW cosine returns a ranked candidate neighbourhood only"
    "typed role, qualifier, provenance, residual, admissibility, and promotion checks remain"

hnswCosineCandidateReceipt :
  Candidate.CandidateOnlyReceipt hnswCosineCandidateRow
hnswCosineCandidateReceipt =
  Candidate.mkCandidateOnlyReceipt
    hnswCosineCandidateRow
    refl refl refl refl refl refl refl refl

hnswCosineCannotPromote :
  Candidate.promoted hnswCosineCandidateRow ≡ false
hnswCosineCannotPromote =
  Candidate.candidatePromotedIsFalse hnswCosineCandidateReceipt

hnswCosineCarriesNoTruthAuthority :
  Candidate.carriesTruthAuthority hnswCosineCandidateRow ≡ false
hnswCosineCarriesNoTruthAuthority =
  Candidate.candidateNoTruthAuthority hnswCosineCandidateReceipt

hnswCosineCarriesNoAdmissibilityAuthority :
  Candidate.carriesAdmissibilityAuthority hnswCosineCandidateRow ≡ false
hnswCosineCarriesNoAdmissibilityAuthority =
  Candidate.candidateNoAdmissibilityAuthority hnswCosineCandidateReceipt

------------------------------------------------------------------------
-- Canonical finite witness.

natCosineProjectionCore : CosineProjectionCore
natCosineProjectionCore =
  mkCosineProjectionCore
    "finite HNSW cosine witness"
    "DASHI.Core.HNSWCosineCandidateLayer"
    Nat
    Nat
    Nat
    (λ n → n)
    (λ left right → left)

canonicalHNSWParameters : HNSWParameters
canonicalHNSWParameters =
  mkHNSWParameters 16 64 32 10

canonicalHNSWQuery : HNSWQuery natCosineProjectionCore
canonicalHNSWQuery =
  mkHNSWQuery
    3
    3
    refl
    canonicalHNSWParameters

canonicalHNSWCandidate :
  HNSWCandidate natCosineProjectionCore canonicalHNSWQuery
canonicalHNSWCandidate =
  mkHNSWCandidate
    5
    5
    refl
    3
    refl
    zero
    zero

canonicalHNSWRetrievalReceipt :
  HNSWRetrievalReceipt natCosineProjectionCore canonicalHNSWQuery
canonicalHNSWRetrievalReceipt =
  mkHNSWRetrievalReceipt
    "canonical finite HNSW candidate receipt"
    (canonicalHNSWCandidate ∷ [])
    true
    refl
    false
    refl
