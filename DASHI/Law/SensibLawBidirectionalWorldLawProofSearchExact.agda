module DASHI.Law.SensibLawBidirectionalWorldLawProofSearchExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Law.SensibLawProofDirectedSearchIntentExact as Intent
import DASHI.Law.SensibLawCorpusProducerRoutingExact as Corpus

------------------------------------------------------------------------
-- BIDIRECTIONAL WORLD <-> LAW SEARCH
--
-- Law -> world: a missing legal element asks which factual proposition and
-- evidence class could pay it.
-- World -> law: a world/factual pattern asks which WrongType/rule consumers
-- might apply, without promoting a candidate WrongType to liability.
------------------------------------------------------------------------

record LawToWorldDemand : Set₁ where
  constructor lawToWorldDemand
  field
    wrongTypeReference : String
    elementReference : String
    missingPropositionShapeReference : String
    requiredProducer : Intent.ProducerClass
    eligibleCorpora : List Corpus.CorpusClass
    actorConstraintReference : String
    temporalConstraintReference : String
    occurrenceConstraintReference : String
    demandReference : String

open LawToWorldDemand public

record WorldPattern : Set₁ where
  constructor worldPattern
  field
    eventReferences : List String
    actorRelationReferences : List String
    harmReferences : List String
    conductReferences : List String
    circumstanceReferences : List String
    temporalReferences : List String
    provenanceReference : String
    patternReference : String

open WorldPattern public

record CandidateWrongTypeConsumer : Set where
  constructor candidateWrongTypeConsumer
  field
    wrongTypeReference : String
    legalSystemReference : String
    structuralMatchReference : String
    authoritySearchRequired : Bool
    applicabilityReviewRequired : Bool
    candidateReference : String

open CandidateWrongTypeConsumer public

record WorldToLawDemand : Set₁ where
  constructor worldToLawDemand
  field
    worldPattern : WorldPattern
    candidateWrongTypes : List CandidateWrongTypeConsumer
    authorityProducer : Intent.ProducerClass
    applicabilityProducer : Intent.ProducerClass
    demandReference : String

open WorldToLawDemand public

------------------------------------------------------------------------
-- Typed meet between a world proposition and a legal requirement remains a
-- candidate comparison until authority/applicability/evidence receipts close.
------------------------------------------------------------------------

record WorldLawCandidateMeet : Set₁ where
  constructor worldLawCandidateMeet
  field
    worldPropositionReference : String
    legalRequirementReference : String
    wrongTypeReference : String
    actorCoordinateReceipt : Set
    conductCoordinateReceipt : Set
    objectCoordinateReceipt : Set
    circumstanceCoordinateReceipt : Set
    temporalCoordinateReceipt : Set
    jurisdictionCoordinateReceipt : Set
    candidateOnly : Bool
    candidateOnlyIsTrue : candidateOnly ≡ true
    meetReference : String

open WorldLawCandidateMeet public

------------------------------------------------------------------------
-- Firewalls.
------------------------------------------------------------------------

data MissingLegalElementMeansSearchMoreLaw : Set where
data WorldPatternAutomaticallySelectsWrongType : Set where
data CandidateWrongTypeAutomaticallyApplicable : Set where
data CandidateWrongTypeAutomaticallyLiability : Set where
data FactualEvidenceAutomaticallyLegalRule : Set where

data LegalRuleAutomaticallyFactualOccurrence : Set where

missingElementNeedNotMeanMoreLaw : MissingLegalElementMeansSearchMoreLaw → ⊥
missingElementNeedNotMeanMoreLaw ()

worldPatternDoesNotSelectWrongType : WorldPatternAutomaticallySelectsWrongType → ⊥
worldPatternDoesNotSelectWrongType ()

candidateWrongTypeDoesNotMeanApplicable : CandidateWrongTypeAutomaticallyApplicable → ⊥
candidateWrongTypeDoesNotMeanApplicable ()

candidateWrongTypeDoesNotMeanLiability : CandidateWrongTypeAutomaticallyLiability → ⊥
candidateWrongTypeDoesNotMeanLiability ()

factualEvidenceDoesNotCreateRule : FactualEvidenceAutomaticallyLegalRule → ⊥
factualEvidenceDoesNotCreateRule ()

legalRuleDoesNotCreateOccurrence : LegalRuleAutomaticallyFactualOccurrence → ⊥
legalRuleDoesNotCreateOccurrence ()

record BidirectionalSearchBoundary : Set where
  constructor bidirectionalSearchBoundary
  field
    lawMayGenerateWorldEvidenceDemand : Bool
    lawMayGenerateWorldEvidenceDemandIsTrue : lawMayGenerateWorldEvidenceDemand ≡ true
    worldMayGenerateCandidateLegalConsumers : Bool
    worldMayGenerateCandidateLegalConsumersIsTrue : worldMayGenerateCandidateLegalConsumers ≡ true
    candidateWrongTypeEqualsLiability : Bool
    candidateWrongTypeEqualsLiabilityIsFalse : candidateWrongTypeEqualsLiability ≡ false
    worldEvidenceEqualsLegalAuthority : Bool
    worldEvidenceEqualsLegalAuthorityIsFalse : worldEvidenceEqualsLegalAuthority ≡ false

canonicalBidirectionalSearchBoundary : BidirectionalSearchBoundary
canonicalBidirectionalSearchBoundary =
  bidirectionalSearchBoundary true refl true refl false refl false refl
